'use strict';
var fs = require('fs');
var path = require('path');
var os = require('os');
var zlib = require('zlib');
var crypto = require('crypto');
var exec = require('child_process').exec;

var TERMINATOR_R = 0x1B;
var TERMINATOR_G = 0x12;
var TERMINATOR_B = 0x12;

var CRC_TABLE = (function buildCrcTable() {
  var table = new Uint32Array(256);
  for (var n = 0; n < 256; n++) {
    var c = n;
    for (var k = 0; k < 8; k++) {
      c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    }
    table[n] = c >>> 0;
  }
  return table;
})();

function crc32(bytes) {
  var crc = 0xFFFFFFFF;
  for (var i = 0; i < bytes.length; i++) {
    crc = CRC_TABLE[(crc ^ bytes[i]) & 0xFF] ^ (crc >>> 8);
  }
  return (crc ^ 0xFFFFFFFF) >>> 0;
}

function paethPredictor(a, b, c) {
  var p = a + b - c;
  var pa = Math.abs(p - a);
  var pb = Math.abs(p - b);
  var pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}

function readPngFile(filePath) {
  var buffer = fs.readFileSync(filePath);
  var signature = [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A];
  for (var s = 0; s < 8; s++) {
    if (buffer[s] !== signature[s]) {
      throw new Error('not a valid PNG file: bad signature');
    }
  }
  var offset = 8;
  var width = 0;
  var height = 0;
  var bitDepth = 0;
  var colorType = 0;
  var idatChunks = [];
  while (offset < buffer.length) {
    if (offset + 8 > buffer.length) {
      throw new Error('truncated PNG: incomplete chunk header');
    }
    var length = buffer.readUInt32BE(offset);
    var type = buffer.toString('ascii', offset + 4, offset + 8);
    var dataStart = offset + 8;
    var dataEnd = dataStart + length;
    if (dataEnd + 4 > buffer.length) {
      throw new Error('truncated PNG: chunk data exceeds file length');
    }
    var chunkData = buffer.subarray(dataStart, dataEnd);
    var storedCrc = buffer.readUInt32BE(dataEnd);
    var crcInput = buffer.subarray(offset + 4, dataEnd);
    var computedCrc = crc32(crcInput);
    if (computedCrc !== storedCrc) {
      throw new Error('corrupted PNG: CRC mismatch in chunk ' + type);
    }
    if (type === 'IHDR') {
      width = chunkData.readUInt32BE(0);
      height = chunkData.readUInt32BE(4);
      bitDepth = chunkData.readUInt8(8);
      colorType = chunkData.readUInt8(9);
      var compressionMethod = chunkData.readUInt8(10);
      var filterMethod = chunkData.readUInt8(11);
      var interlaceMethod = chunkData.readUInt8(12);
      if (bitDepth !== 8) {
        throw new Error('unsupported PNG bit depth: ' + bitDepth);
      }
      if (colorType !== 2 && colorType !== 6) {
        throw new Error('unsupported PNG color type: ' + colorType);
      }
      if (compressionMethod !== 0) {
        throw new Error('unsupported PNG compression method: ' + compressionMethod);
      }
      if (filterMethod !== 0) {
        throw new Error('unsupported PNG filter method: ' + filterMethod);
      }
      if (interlaceMethod !== 0) {
        throw new Error('unsupported interlaced PNG (Adam7 not supported)');
      }
    } else if (type === 'IDAT') {
      idatChunks.push(chunkData);
    } else if (type === 'IEND') {
      offset = dataEnd + 4;
      break;
    }
    offset = dataEnd + 4;
  }
  if (width === 0 || height === 0) {
    throw new Error('invalid PNG: missing IHDR');
  }
  if (idatChunks.length === 0) {
    throw new Error('invalid PNG: no image data');
  }
  var compressed = Buffer.concat(idatChunks);
  var raw = zlib.inflateSync(compressed);
  var bytesPerPixel = colorType === 6 ? 4 : 3;
  var rowBytes = width * bytesPerPixel;
  if (raw.length !== height * (rowBytes + 1)) {
    throw new Error('corrupted PNG: unexpected decompressed size');
  }
  var pixels = new Uint8Array(width * height * bytesPerPixel);
  var rawOffset = 0;
  var priorRowStart = -1;
  for (var y = 0; y < height; y++) {
    var filterType = raw[rawOffset];
    rawOffset += 1;
    var rowStart = y * rowBytes;
    for (var x = 0; x < rowBytes; x++) {
      var rawByte = raw[rawOffset + x];
      var a = x >= bytesPerPixel ? pixels[rowStart + x - bytesPerPixel] : 0;
      var b = priorRowStart >= 0 ? pixels[priorRowStart + x] : 0;
      var c = (priorRowStart >= 0 && x >= bytesPerPixel) ? pixels[priorRowStart + x - bytesPerPixel] : 0;
      var reconByte;
      if (filterType === 0) {
        reconByte = rawByte;
      } else if (filterType === 1) {
        reconByte = (rawByte + a) & 0xFF;
      } else if (filterType === 2) {
        reconByte = (rawByte + b) & 0xFF;
      } else if (filterType === 3) {
        reconByte = (rawByte + Math.floor((a + b) / 2)) & 0xFF;
      } else if (filterType === 4) {
        reconByte = (rawByte + paethPredictor(a, b, c)) & 0xFF;
      } else {
        throw new Error('unsupported PNG filter type: ' + filterType);
      }
      pixels[rowStart + x] = reconByte;
    }
    rawOffset += rowBytes;
    priorRowStart = rowStart;
  }
  return { width: width, height: height, bytesPerPixel: bytesPerPixel, pixels: pixels };
}

function decodeSourceFromPixels(width, height, bytesPerPixel, pixels) {
  var outBytes = [];
  var totalPixels = width * height;
  var terminated = false;
  for (var p = 0; p < totalPixels; p++) {
    var offset = p * bytesPerPixel;
    var r = pixels[offset];
    var g = pixels[offset + 1];
    var b = pixels[offset + 2];
    if (r === TERMINATOR_R && g === TERMINATOR_G && b === TERMINATOR_B) {
      terminated = true;
      break;
    }
    if (r !== g || g !== b) {
      throw new Error('invalid program image: unrecognized pixel at index ' + p + ' (' + r + ',' + g + ',' + b + ')');
    }
    outBytes.push(r);
  }
  if (!terminated) {
    throw new Error('invalid program image: terminator pixel #1B1212 not found');
  }
  return Buffer.from(outBytes).toString('utf8');
}

function openInBrowser(filePath) {
  var platform = process.platform;
  var command;
  if (platform === 'darwin') {
    command = 'open "' + filePath + '"';
  } else if (platform === 'win32') {
    command = 'start "" "' + filePath + '"';
  } else {
    command = 'xdg-open "' + filePath + '"';
  }
  exec(command, function (err) {
    if (err) {
      console.error('could not auto-open a browser, open this file manually: ' + filePath);
    }
  });
}

function main() {
  var inputPath = process.argv[2] || path.join(__dirname, 'image.png');
  if (!fs.existsSync(inputPath)) {
    throw new Error('image not found: ' + inputPath);
  }
  var decoded = readPngFile(inputPath);
  var source = decodeSourceFromPixels(decoded.width, decoded.height, decoded.bytesPerPixel, decoded.pixels);
  var tempPath = path.join(os.tmpdir(), 'forged-' + Date.now() + '-' + crypto.randomBytes(4).toString('hex') + '.html');
  fs.writeFileSync(tempPath, source, 'utf8');
  console.log('decoded ' + decoded.width + 'x' + decoded.height + ' image -> ' + Buffer.byteLength(source, 'utf8') + ' bytes of source');
  console.log('running: ' + tempPath);
  openInBrowser(tempPath);
}

try {
  main();
} catch (err) {
  console.error('failed: ' + err.message);
  process.exit(1);
}
