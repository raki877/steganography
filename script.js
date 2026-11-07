/* ======================================================================
   STEGANOGRAPHY STUDIO — APPLICATION LOGIC
   100% client-side. Nothing here ever sends data anywhere.

   Contents:
     1. Constants & small utilities
     2. Custom error type
     3. Bit-level helpers (byte <-> bit conversion)
     4. LSB steganography engine (embed / extract / encode / decode)
     5. AES-256-GCM password encryption (Web Crypto API)
     6. DOM references
     7. Theme toggle
     8. Tab switching
     9. Toast notifications
    10. File loading & validation helpers
    11. Drag-and-drop wiring
    12. "Hide Message" tab wiring
    13. "Reveal Message" tab wiring
    14. Boot
   ====================================================================== */

(() => {
  "use strict";

  /* ----------------------------------------------------------------
     1. CONSTANTS & SMALL UTILITIES
     ---------------------------------------------------------------- */

  // Header layout embedded before every hidden message:
  //   4 bytes  magic signature "STEG"   -> lets us recognise our own images
  //   1 byte   flag                     -> bit0: 1 = AES-encrypted payload
  //   4 bytes  payload length (uint32, big-endian)
  const HEADER_MAGIC = 0x53544547; // 'S' 'T' 'E' 'G'
  const HEADER_BYTES = 9;

  // AES-GCM packaging: [salt][iv][ciphertext+tag]
  const SALT_LENGTH = 16;
  const IV_LENGTH = 12;
  const GCM_TAG_LENGTH = 16; // appended to ciphertext automatically by WebCrypto
  const PBKDF2_ITERATIONS = 150000;

  const MAX_FILE_SIZE = 25 * 1024 * 1024; // 25 MB safety cap

  const wait = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

  /** Format a byte count as a short human-readable string. */
  function formatBytes(bytes) {
    if (bytes < 1024) return `${bytes} B`;
    if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
    return `${(bytes / (1024 * 1024)).toFixed(2)} MB`;
  }

  function uint32ToBytes(num) {
    return [
      (num >>> 24) & 0xff,
      (num >>> 16) & 0xff,
      (num >>> 8) & 0xff,
      num & 0xff,
    ];
  }

  function bytesToUint32(bytes, offset = 0) {
    return (
      ((bytes[offset] << 24) |
        (bytes[offset + 1] << 16) |
        (bytes[offset + 2] << 8) |
        bytes[offset + 3]) >>>
      0
    );
  }

  /* ----------------------------------------------------------------
     2. CUSTOM ERROR TYPE
     ---------------------------------------------------------------- */

  class StegoError extends Error {
    constructor(code, message) {
      super(message);
      this.name = "StegoError";
      this.code = code;
    }
  }

  const ERROR_TITLES = {
    NO_FILE: "No image selected",
    INVALID_TYPE: "Unsupported file type",
    TOO_LARGE: "Image too large",
    DECODE_FAILED: "Could not read image",
    READ_FAILED: "Could not read file",
    NO_IMAGE: "Image required",
    EMPTY_MESSAGE: "Message required",
    NO_PASSWORD: "Password required",
    CAPACITY_EXCEEDED: "Message too large",
    NOT_STEGO_IMAGE: "No hidden message found",
    CORRUPTED: "Image appears compressed or corrupted",
    PASSWORD_REQUIRED: "Password needed",
    WRONG_PASSWORD: "Incorrect password",
    CRYPTO_UNAVAILABLE: "Encryption unavailable",
  };

  /* ----------------------------------------------------------------
     3. BIT-LEVEL HELPERS
     ---------------------------------------------------------------- */

  /** Expand bytes into individual bits, most-significant bit first. */
  function bytesToBits(bytes) {
    const bits = new Uint8Array(bytes.length * 8);
    for (let i = 0; i < bytes.length; i++) {
      for (let b = 0; b < 8; b++) {
        bits[i * 8 + b] = (bytes[i] >> (7 - b)) & 1;
      }
    }
    return bits;
  }

  /** Pack a whole number of bytes' worth of bits back into a Uint8Array. */
  function bitsToBytes(bits) {
    const byteLen = Math.floor(bits.length / 8);
    const bytes = new Uint8Array(byteLen);
    for (let i = 0; i < byteLen; i++) {
      let value = 0;
      for (let b = 0; b < 8; b++) {
        value = (value << 1) | bits[i * 8 + b];
      }
      bytes[i] = value;
    }
    return bytes;
  }

  /* ----------------------------------------------------------------
     4. LSB STEGANOGRAPHY ENGINE
     ---------------------------------------------------------------- */

  // We only ever touch the R, G and B channels of each pixel (never alpha),
  // flipping just the least-significant bit of each — a change of at most
  // 1/255 in brightness per channel, invisible to the human eye.

  /** How many R/G/B channels (not counting alpha) exist in this image data. */
  function usableChannelCount(imageData) {
    return Math.floor(imageData.data.length / 4) * 3;
  }

  /** Mutates imageData in place, writing `bits` into successive colour channels. */
  function embedBitsIntoImageData(imageData, bits) {
    const data = imageData.data;
    const capacity = usableChannelCount(imageData);
    if (bits.length > capacity) {
      throw new StegoError(
        "CAPACITY_EXCEEDED",
        "The message is larger than this image can hold.",
      );
    }
    for (let i = 0; i < bits.length; i++) {
      const pixelIndex = Math.floor(i / 3);
      const channel = i % 3; // 0 = R, 1 = G, 2 = B
      const dataIndex = pixelIndex * 4 + channel;
      data[dataIndex] = (data[dataIndex] & 0xfe) | bits[i];
    }
  }

  /** Reads back `numBits` least-significant bits from successive colour channels. */
  function extractBitsFromImageData(imageData, numBits) {
    const data = imageData.data;
    const bits = new Uint8Array(numBits);
    for (let i = 0; i < numBits; i++) {
      const pixelIndex = Math.floor(i / 3);
      const channel = i % 3;
      const dataIndex = pixelIndex * 4 + channel;
      bits[i] = data[dataIndex] & 1;
    }
    return bits;
  }

  /**
   * Encodes `message` into `imageData` in place.
   * If `password` is truthy, the message is AES-256-GCM encrypted first.
   */
  async function encodeMessageIntoImageData(
    imageData,
    message,
    password,
    robust = false,
  ) {
    const encoder = new TextEncoder();
    let payloadBytes;
    let flag = 0;

    if (password) {
      payloadBytes = await encryptMessage(message, password);
      flag = 1;
    } else {
      payloadBytes = encoder.encode(message);
    }

    // Robust mode: survives JPEG re-compression (WhatsApp, Instagram, ...).
    if (robust) {
      robustEmbed(imageData, payloadBytes, flag);
      return;
    }

    const header = new Uint8Array(HEADER_BYTES);
    header.set(uint32ToBytes(HEADER_MAGIC), 0);
    header[4] = flag;
    header.set(uint32ToBytes(payloadBytes.length), 5);

    const fullBytes = new Uint8Array(HEADER_BYTES + payloadBytes.length);
    fullBytes.set(header, 0);
    fullBytes.set(payloadBytes, HEADER_BYTES);

    const bits = bytesToBits(fullBytes);
    const capacity = usableChannelCount(imageData);
    if (bits.length > capacity) {
      throw new StegoError(
        "CAPACITY_EXCEEDED",
        `This message needs ${formatBytes(fullBytes.length)} but this image can only hold ${formatBytes(Math.floor(capacity / 8))}.`,
      );
    }

    embedBitsIntoImageData(imageData, bits);
  }

  /**
   * Decodes a hidden message from `imageData`.
   * `password` may be null if the message is not expected to be encrypted.
   * Throws a StegoError with a specific `.code` for every failure mode.
   */
  async function decodeMessageFromImageData(imageData, password) {
    const capacity = usableChannelCount(imageData);
    const headerBitCount = HEADER_BYTES * 8;

    // 1) Classic lossless LSB message?
    if (capacity >= headerBitCount) {
      const headerBits = extractBitsFromImageData(imageData, headerBitCount);
      const headerBytes = bitsToBytes(headerBits);
      if (bytesToUint32(headerBytes, 0) === HEADER_MAGIC) {
        const flag = headerBytes[4];
        const payloadLength = bytesToUint32(headerBytes, 5);
        const totalBitsNeeded = headerBitCount + payloadLength * 8;
        if (totalBitsNeeded > capacity) {
          throw new StegoError(
            "CORRUPTED",
            "The hidden data looks incomplete or corrupted.",
          );
        }
        const allBits = extractBitsFromImageData(imageData, totalBitsNeeded);
        const payloadBytes = bitsToBytes(allBits.slice(headerBitCount));
        return finishDecode(flag, payloadBytes, password);
      }
    }

    // 2) Robust message (survives WhatsApp / JPEG compression)?
    const robust = robustExtract(imageData);
    if (robust) return finishDecode(robust.flag, robust.payload, password);

    throw new StegoError(
      "NOT_STEGO_IMAGE",
      "No hidden message was found. This image was not created with Steganography Studio, or it was altered too much (resized, cropped, or edited) after the message was hidden.",
    );
  }

  /** Shared last step: decrypt if needed and turn bytes into text. */
  async function finishDecode(flag, payloadBytes, password) {
    if (flag === 1) {
      if (!password) {
        throw new StegoError(
          "PASSWORD_REQUIRED",
          "This message is password-protected. Enter the password to reveal it.",
        );
      }
      let plainBytes;
      try {
        plainBytes = await decryptMessage(payloadBytes, password);
      } catch (err) {
        throw new StegoError(
          "WRONG_PASSWORD",
          "Incorrect password, or the image data is corrupted.",
        );
      }
      return new TextDecoder().decode(plainBytes);
    }
    return new TextDecoder().decode(payloadBytes);
  }

  /* ----------------------------------------------------------------
     4b. ROBUST ENGINE  (survives JPEG re-compression, e.g. WhatsApp)
     ----------------------------------------------------------------
     Plain LSB hiding is destroyed by any lossy re-compression. This engine
     instead hides each bit in the *average brightness* of an 8x8 pixel block
     (quantisation index modulation, QIM). A block's average brightness barely
     changes when JPEG squeezes the image, so the bits survive. On top of that:
       - every bit is stored several times in pseudo-randomly scattered blocks
         and the copies are combined by soft voting,
       - the data is protected with Reed-Solomon error correction.
     ---------------------------------------------------------------- */

  const ROBUST_BLOCK = 8;
  const ROBUST_STEP = 12; // QIM lattice spacing (brightness levels)
  const ROBUST_MAX_DIM = 1280; // WhatsApp "standard" resizes anything bigger
  const ROBUST_MAGIC = [0x53, 0x42]; // "SB"
  const ROBUST_HDR_DATA = 6; // magic(2) + flag(1) + length(3)
  const ROBUST_HDR_PARITY = 16;
  const ROBUST_HDR_REPEAT = 9;
  const ROBUST_RS_CHUNK = 200; // data bytes per Reed-Solomon block
  const ROBUST_RS_PARITY = 32; // parity bytes per block (fixes 16 bad bytes)
  const ROBUST_MIN_REPEAT = 3;
  const ROBUST_MAX_REPEAT = 15;
  const ROBUST_HDR_BLOCKS =
    (ROBUST_HDR_DATA + ROBUST_HDR_PARITY) * 8 * ROBUST_HDR_REPEAT;

  /* ---- Reed-Solomon over GF(256) (primitive polynomial 0x11d) ---- */
  const GF_EXP = new Uint8Array(512);
  const GF_LOG = new Uint8Array(256);
  (function initGF() {
    let x = 1;
    for (let i = 0; i < 255; i++) {
      GF_EXP[i] = x;
      GF_LOG[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= 0x11d;
    }
    for (let i = 255; i < 512; i++) GF_EXP[i] = GF_EXP[i - 255];
  })();

  const gfMul = (a, b) => (a && b ? GF_EXP[GF_LOG[a] + GF_LOG[b]] : 0);
  const gfDiv = (a, b) => (a ? GF_EXP[(GF_LOG[a] + 255 - GF_LOG[b]) % 255] : 0);
  const gfInv = (a) => GF_EXP[255 - GF_LOG[a]];

  const rsGenCache = {};
  function rsGenerator(nsym) {
    if (rsGenCache[nsym]) return rsGenCache[nsym];
    let g = [1]; // highest degree first
    for (let i = 0; i < nsym; i++) {
      const next = new Array(g.length + 1).fill(0);
      for (let j = 0; j < g.length; j++) {
        next[j] ^= g[j];
        next[j + 1] ^= gfMul(g[j], GF_EXP[i]);
      }
      g = next;
    }
    return (rsGenCache[nsym] = g);
  }

  /** Returns data followed by `nsym` parity bytes. */
  function rsEncode(data, nsym) {
    const gen = rsGenerator(nsym);
    const out = new Uint8Array(data.length + nsym);
    out.set(data, 0);
    for (let i = 0; i < data.length; i++) {
      const coef = out[i];
      if (coef !== 0) {
        for (let j = 1; j < gen.length; j++) out[i + j] ^= gfMul(gen[j], coef);
      }
    }
    out.set(data, 0); // restore data (the loop above used it as scratch)
    return out;
  }

  /** Corrects up to nsym/2 wrong bytes. Returns the data part, or null if hopeless. */
  function rsDecode(received, nsym) {
    const n = received.length;
    const r = Uint8Array.from(received);

    // syndromes S_j = r(alpha^j)
    const synd = new Array(nsym).fill(0);
    let clean = true;
    for (let j = 0; j < nsym; j++) {
      let s = 0;
      for (let i = 0; i < n; i++) s = gfMul(s, GF_EXP[j]) ^ r[i];
      synd[j] = s;
      if (s) clean = false;
    }
    if (clean) return r.slice(0, n - nsym);

    // Berlekamp-Massey -> error locator (lowest degree first)
    let C = [1];
    let B = [1];
    let L = 0;
    let m = 1;
    let b = 1;
    for (let i = 0; i < nsym; i++) {
      let d = synd[i];
      for (let k = 1; k <= L; k++) d ^= gfMul(C[k] || 0, synd[i - k]);
      if (d === 0) {
        m++;
      } else if (2 * L <= i) {
        const T = C.slice();
        const coef = gfDiv(d, b);
        while (C.length < B.length + m) C.push(0);
        for (let k = 0; k < B.length; k++) C[k + m] ^= gfMul(coef, B[k]);
        L = i + 1 - L;
        B = T;
        b = d;
        m = 1;
      } else {
        const coef = gfDiv(d, b);
        while (C.length < B.length + m) C.push(0);
        for (let k = 0; k < B.length; k++) C[k + m] ^= gfMul(coef, B[k]);
        m++;
      }
    }
    while (C.length > 1 && C[C.length - 1] === 0) C.pop();
    if (L * 2 > nsym || C.length - 1 !== L) return null;

    // Chien search: error at array index p has locator X = alpha^(n-1-p)
    const errPos = [];
    for (let p = 0; p < n; p++) {
      const xInvExp = (255 - ((n - 1 - p) % 255)) % 255; // alpha^-(n-1-p)
      let v = 0;
      for (let k = 0; k < C.length; k++) {
        v ^= gfMul(C[k], GF_EXP[(xInvExp * k) % 255]);
      }
      if (v === 0) errPos.push(p);
    }
    if (errPos.length !== L) return null;

    // Error evaluator: Omega = S(x) * Lambda(x) mod x^nsym
    const omega = new Array(nsym).fill(0);
    for (let i = 0; i < nsym; i++) {
      for (let k = 0; k < C.length && k <= i; k++) {
        omega[i] ^= gfMul(C[k], synd[i - k]);
      }
    }

    // Forney: e = X * Omega(X^-1) / Lambda'(X^-1)
    for (const p of errPos) {
      const xExp = (n - 1 - p) % 255;
      const xInvExp = (255 - xExp) % 255;
      let om = 0;
      for (let k = 0; k < omega.length; k++) {
        om ^= gfMul(omega[k], GF_EXP[(xInvExp * k) % 255]);
      }
      let dl = 0;
      for (let k = 1; k < C.length; k += 2) {
        dl ^= gfMul(C[k], GF_EXP[(xInvExp * (k - 1)) % 255]);
      }
      if (dl === 0) return null;
      r[p] ^= gfDiv(gfMul(GF_EXP[xExp], om), dl);
    }

    // verify
    for (let j = 0; j < nsym; j++) {
      let s = 0;
      for (let i = 0; i < n; i++) s = gfMul(s, GF_EXP[j]) ^ r[i];
      if (s) return null;
    }
    return r.slice(0, n - nsym);
  }

  /** Splits data into chunks and RS-protects each one. */
  function rsEncodeChunks(data) {
    const chunks = [];
    for (let off = 0; off < data.length; off += ROBUST_RS_CHUNK) {
      chunks.push(
        rsEncode(data.slice(off, off + ROBUST_RS_CHUNK), ROBUST_RS_PARITY),
      );
    }
    const out = new Uint8Array(robustCodedLength(data.length));
    let pos = 0;
    for (const c of chunks) {
      out.set(c, pos);
      pos += c.length;
    }
    return out;
  }

  function rsDecodeChunks(coded, dataLength) {
    const out = new Uint8Array(dataLength);
    let inPos = 0;
    let outPos = 0;
    while (outPos < dataLength) {
      const k = Math.min(ROBUST_RS_CHUNK, dataLength - outPos);
      const block = coded.slice(inPos, inPos + k + ROBUST_RS_PARITY);
      const fixed = rsDecode(block, ROBUST_RS_PARITY);
      if (!fixed) return null;
      out.set(fixed, outPos);
      inPos += k + ROBUST_RS_PARITY;
      outPos += k;
    }
    return out;
  }

  function robustCodedLength(dataLength) {
    return dataLength + ROBUST_RS_PARITY * Math.ceil(dataLength / ROBUST_RS_CHUNK);
  }

  /* ---- Block geometry ---- */

  function robustBlockCount(width, height) {
    return Math.floor(width / ROBUST_BLOCK) * Math.floor(height / ROBUST_BLOCK);
  }

  /** Largest payload (bytes) that fits, using at least ROBUST_MIN_REPEAT copies. */
  function robustCapacityBytes(width, height) {
    const avail = robustBlockCount(width, height) - ROBUST_HDR_BLOCKS;
    if (avail <= 0) return 0;
    const codedMax = Math.floor(avail / (8 * ROBUST_MIN_REPEAT));
    let k = Math.max(0, codedMax - ROBUST_RS_PARITY * Math.ceil(codedMax / ROBUST_RS_CHUNK));
    while (k > 0 && robustCodedLength(k) > codedMax) k--;
    return Math.min(k, 0xffffff);
  }

  /** Deterministic pseudo-random order of the blocks (same for hide and reveal). */
  function robustBlockOrder(count) {
    const order = new Uint32Array(count);
    for (let i = 0; i < count; i++) order[i] = i;
    let seed = 0x5eedb10c >>> 0;
    const rand = () => {
      seed = (seed + 0x6d2b79f5) >>> 0;
      let t = seed;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    for (let i = count - 1; i > 0; i--) {
      const j = Math.floor(rand() * (i + 1));
      const tmp = order[i];
      order[i] = order[j];
      order[j] = tmp;
    }
    return order;
  }

  function robustRepeatFor(codedBytes, blockCount) {
    const avail = blockCount - ROBUST_HDR_BLOCKS;
    return Math.min(ROBUST_MAX_REPEAT, Math.floor(avail / (codedBytes * 8)));
  }

  /* ---- Per-block brightness ---- */

  function blockLuma(data, width, bx, by) {
    let sum = 0;
    for (let y = 0; y < ROBUST_BLOCK; y++) {
      let idx = ((by * ROBUST_BLOCK + y) * width + bx * ROBUST_BLOCK) * 4;
      for (let x = 0; x < ROBUST_BLOCK; x++, idx += 4) {
        sum += 0.299 * data[idx] + 0.587 * data[idx + 1] + 0.114 * data[idx + 2];
      }
    }
    return sum / (ROBUST_BLOCK * ROBUST_BLOCK);
  }

  /** Brightness of the block after adding `shift` to R, G and B (with clamping). */
  function shiftedLuma(data, width, bx, by, shift) {
    let sum = 0;
    for (let y = 0; y < ROBUST_BLOCK; y++) {
      let idx = ((by * ROBUST_BLOCK + y) * width + bx * ROBUST_BLOCK) * 4;
      for (let x = 0; x < ROBUST_BLOCK; x++, idx += 4) {
        const r = Math.min(255, Math.max(0, data[idx] + shift));
        const g = Math.min(255, Math.max(0, data[idx + 1] + shift));
        const b = Math.min(255, Math.max(0, data[idx + 2] + shift));
        sum += 0.299 * r + 0.587 * g + 0.114 * b;
      }
    }
    return sum / (ROBUST_BLOCK * ROBUST_BLOCK);
  }

  function applyShift(data, width, bx, by, shift) {
    for (let y = 0; y < ROBUST_BLOCK; y++) {
      let idx = ((by * ROBUST_BLOCK + y) * width + bx * ROBUST_BLOCK) * 4;
      for (let x = 0; x < ROBUST_BLOCK; x++, idx += 4) {
        data[idx] = Math.min(255, Math.max(0, data[idx] + shift));
        data[idx + 1] = Math.min(255, Math.max(0, data[idx + 1] + shift));
        data[idx + 2] = Math.min(255, Math.max(0, data[idx + 2] + shift));
      }
    }
  }

  /** Lattice point for `bit` nearest to `m`, offset by `k` lattice steps. */
  function qimTarget(m, bit, k) {
    const half = bit ? ROBUST_STEP / 2 : 0;
    return (Math.round((m - half) / ROBUST_STEP) + k) * ROBUST_STEP + half;
  }

  /** Writes one bit into one block by nudging its brightness onto the bit's lattice. */
  function embedBitInBlock(data, width, bx, by, bit) {
    const m = blockLuma(data, width, bx, by);
    let best = 0;
    let bestErr = Infinity;
    for (const k of [0, 1, -1]) {
      const shift = Math.round(qimTarget(m, bit, k) - m);
      const achieved = shiftedLuma(data, width, bx, by, shift);
      // error measured on the lattice of the wanted bit
      const err = Math.abs(achieved - qimTarget(achieved, bit, 0));
      if (err < bestErr - 1e-9) {
        bestErr = err;
        best = shift;
        if (err < 1) break;
      }
    }
    if (best !== 0) applyShift(data, width, bx, by, best);
  }

  /** Soft value in [-1, 1]: positive => bit 1, negative => bit 0. */
  function qimSoft(m) {
    const d0 = Math.abs(m - Math.round(m / ROBUST_STEP) * ROBUST_STEP);
    const h = ROBUST_STEP / 2;
    const d1 = Math.abs(m - (Math.round((m - h) / ROBUST_STEP) * ROBUST_STEP + h));
    return (d0 - d1) / (ROBUST_STEP / 4);
  }

  function bytesFromSoft(soft) {
    const out = new Uint8Array(Math.floor(soft.length / 8));
    for (let i = 0; i < out.length; i++) {
      let v = 0;
      for (let b = 0; b < 8; b++) v = (v << 1) | (soft[i * 8 + b] > 0 ? 1 : 0);
      out[i] = v;
    }
    return out;
  }

  /* ---- Public robust API ---- */

  /** Mutates imageData in place. `flag` bit0 = payload is AES encrypted. */
  function robustEmbed(imageData, payloadBytes, flag) {
    const { width, height, data } = imageData;
    const nbx = Math.floor(width / ROBUST_BLOCK);
    const total = robustBlockCount(width, height);

    if (payloadBytes.length > robustCapacityBytes(width, height)) {
      throw new StegoError(
        "CAPACITY_EXCEEDED",
        "The message is larger than this image can hold in WhatsApp-safe mode.",
      );
    }

    const len = payloadBytes.length;
    const header = new Uint8Array([
      ROBUST_MAGIC[0],
      ROBUST_MAGIC[1],
      flag & 0xff,
      (len >>> 16) & 0xff,
      (len >>> 8) & 0xff,
      len & 0xff,
    ]);
    const headerCoded = rsEncode(header, ROBUST_HDR_PARITY);
    const payloadCoded = rsEncodeChunks(payloadBytes);
    const repeat = robustRepeatFor(payloadCoded.length, total);
    const order = robustBlockOrder(total);

    const put = (slot, bit) => {
      const blockIndex = order[slot];
      embedBitInBlock(data, width, blockIndex % nbx, Math.floor(blockIndex / nbx), bit);
    };

    // header: every bit repeated ROBUST_HDR_REPEAT times
    let slot = 0;
    for (let i = 0; i < headerCoded.length * 8; i++) {
      const bit = (headerCoded[i >> 3] >> (7 - (i & 7))) & 1;
      for (let c = 0; c < ROBUST_HDR_REPEAT; c++) put(slot++, bit);
    }
    // payload: every bit repeated `repeat` times
    for (let i = 0; i < payloadCoded.length * 8; i++) {
      const bit = (payloadCoded[i >> 3] >> (7 - (i & 7))) & 1;
      for (let c = 0; c < repeat; c++) put(slot++, bit);
    }
  }

  /**
   * Looks for a robust-mode message. Returns { flag, payload } or null when the
   * image has no such header at all. Throws CORRUPTED if the header is present
   * but the body could not be recovered.
   */
  function robustExtract(imageData) {
    const { width, height, data } = imageData;
    const nbx = Math.floor(width / ROBUST_BLOCK);
    const total = robustBlockCount(width, height);
    if (total <= ROBUST_HDR_BLOCKS) return null;

    const order = robustBlockOrder(total);
    const lumaCache = new Map();
    const softAt = (slot) => {
      const blockIndex = order[slot];
      let v = lumaCache.get(blockIndex);
      if (v === undefined) {
        v = qimSoft(blockLuma(data, width, blockIndex % nbx, Math.floor(blockIndex / nbx)));
        lumaCache.set(blockIndex, v);
      }
      return v;
    };

    // header
    const hdrBits = (ROBUST_HDR_DATA + ROBUST_HDR_PARITY) * 8;
    const hdrSoft = new Float32Array(hdrBits);
    let slot = 0;
    for (let i = 0; i < hdrBits; i++) {
      let s = 0;
      for (let c = 0; c < ROBUST_HDR_REPEAT; c++) s += softAt(slot++);
      hdrSoft[i] = s;
    }
    const header = rsDecode(bytesFromSoft(hdrSoft), ROBUST_HDR_PARITY);
    if (!header || header[0] !== ROBUST_MAGIC[0] || header[1] !== ROBUST_MAGIC[1]) {
      return null;
    }
    const flag = header[2];
    const len = (header[3] << 16) | (header[4] << 8) | header[5];

    // payload
    const codedLen = robustCodedLength(len);
    const repeat = robustRepeatFor(codedLen, total);
    if (len === 0 || repeat < ROBUST_MIN_REPEAT) {
      throw new StegoError("CORRUPTED", "The hidden data looks incomplete or corrupted.");
    }
    const soft = new Float32Array(codedLen * 8);
    for (let i = 0; i < soft.length; i++) {
      let s = 0;
      for (let c = 0; c < repeat; c++) s += softAt(slot++);
      soft[i] = s;
    }
    const payload = rsDecodeChunks(bytesFromSoft(soft), len);
    if (!payload) {
      throw new StegoError("CORRUPTED", "The hidden data looks incomplete or corrupted.");
    }
    return { flag, payload };
  }

  /* ----------------------------------------------------------------
     5. AES-256-GCM PASSWORD ENCRYPTION
     ---------------------------------------------------------------- */

  const hasWebCrypto = !!(window.crypto && window.crypto.subtle);

  async function deriveKey(password, salt) {
    const keyMaterial = await crypto.subtle.importKey(
      "raw",
      new TextEncoder().encode(password),
      "PBKDF2",
      false,
      ["deriveKey"],
    );
    return crypto.subtle.deriveKey(
      { name: "PBKDF2", salt, iterations: PBKDF2_ITERATIONS, hash: "SHA-256" },
      keyMaterial,
      { name: "AES-GCM", length: 256 },
      false,
      ["encrypt", "decrypt"],
    );
  }

  /** Returns Uint8Array: [salt(16)][iv(12)][ciphertext+tag]. */
  async function encryptMessage(message, password) {
    if (!hasWebCrypto) {
      throw new StegoError(
        "CRYPTO_UNAVAILABLE",
        "Your browser does not support the Web Crypto API needed for encryption.",
      );
    }
    const salt = crypto.getRandomValues(new Uint8Array(SALT_LENGTH));
    const iv = crypto.getRandomValues(new Uint8Array(IV_LENGTH));
    const key = await deriveKey(password, salt);
    const cipherBuffer = await crypto.subtle.encrypt(
      { name: "AES-GCM", iv },
      key,
      new TextEncoder().encode(message),
    );
    const cipherBytes = new Uint8Array(cipherBuffer);

    const combined = new Uint8Array(
      salt.length + iv.length + cipherBytes.length,
    );
    combined.set(salt, 0);
    combined.set(iv, salt.length);
    combined.set(cipherBytes, salt.length + iv.length);
    return combined;
  }

  /** Reverses encryptMessage(). Throws if the password is wrong (auth tag fails). */
  async function decryptMessage(payloadBytes, password) {
    const salt = payloadBytes.slice(0, SALT_LENGTH);
    const iv = payloadBytes.slice(SALT_LENGTH, SALT_LENGTH + IV_LENGTH);
    const cipherBytes = payloadBytes.slice(SALT_LENGTH + IV_LENGTH);
    const key = await deriveKey(password, salt);
    const plainBuffer = await crypto.subtle.decrypt(
      { name: "AES-GCM", iv },
      key,
      cipherBytes,
    );
    return new Uint8Array(plainBuffer);
  }

  /* ----------------------------------------------------------------
     6. DOM REFERENCES
     ---------------------------------------------------------------- */

  const root = document.documentElement;
  const themeToggle = document.getElementById("themeToggle");

  const tabHide = document.getElementById("tab-hide");
  const tabReveal = document.getElementById("tab-reveal");
  const tabIndicator = document.querySelector(".tab-indicator");
  const panelHide = document.getElementById("panel-hide");
  const panelReveal = document.getElementById("panel-reveal");

  const toastContainer = document.getElementById("toastContainer");

  // Hide tab
  const hideDropzone = document.getElementById("hideDropzone");
  const hideFileInput = document.getElementById("hideFileInput");
  const hidePreviewWrap = document.getElementById("hidePreviewWrap");
  const hidePreviewImg = document.getElementById("hidePreviewImg");
  const hideRemoveImg = document.getElementById("hideRemoveImg");
  const hideImgDims = document.getElementById("hideImgDims");
  const hideImgSize = document.getElementById("hideImgSize");
  const hideMessageInput = document.getElementById("hideMessageInput");
  const hideCharCount = document.getElementById("hideCharCount");
  const hideByteCount = document.getElementById("hideByteCount");
  const hideCapacityTrack = document.getElementById("hideCapacityTrack");
  const hideCapacityFill = document.getElementById("hideCapacityFill");
  const hideCapacityHint = document.getElementById("hideCapacityHint");
  const hideEncryptToggle = document.getElementById("hideEncryptToggle");
  const hideRobustToggle = document.getElementById("hideRobustToggle");
  const hidePasswordWrap = document.getElementById("hidePasswordWrap");
  const hidePasswordInput = document.getElementById("hidePasswordInput");
  const hidePasswordVisibility = document.getElementById(
    "hidePasswordVisibility",
  );
  const hideSubmitBtn = document.getElementById("hideSubmitBtn");

  // Reveal tab
  const revealDropzone = document.getElementById("revealDropzone");
  const revealFileInput = document.getElementById("revealFileInput");
  const revealPreviewWrap = document.getElementById("revealPreviewWrap");
  const revealPreviewImg = document.getElementById("revealPreviewImg");
  const revealRemoveImg = document.getElementById("revealRemoveImg");
  const revealImgDims = document.getElementById("revealImgDims");
  const revealImgSize = document.getElementById("revealImgSize");
  const revealPasswordInput = document.getElementById("revealPasswordInput");
  const revealPasswordVisibility = document.getElementById(
    "revealPasswordVisibility",
  );
  const revealSubmitBtn = document.getElementById("revealSubmitBtn");
  const revealOutputWrap = document.getElementById("revealOutputWrap");
  const revealOutputText = document.getElementById("revealOutputText");
  const revealCopyBtn = document.getElementById("revealCopyBtn");

  // Per-tab application state
  const state = {
    hide: { file: null, fileName: "", imageData: null, capacityBytes: 0 },
    reveal: { file: null, imageData: null, lastMessage: "" },
  };

  const prefersReducedMotion = window.matchMedia(
    "(prefers-reduced-motion: reduce)",
  ).matches;

  /* ----------------------------------------------------------------
     7. THEME TOGGLE
     ---------------------------------------------------------------- */

  function applyTheme(theme) {
    root.setAttribute("data-theme", theme);
    themeToggle.setAttribute("aria-pressed", String(theme === "light"));
    themeToggle.setAttribute(
      "aria-label",
      theme === "light" ? "Switch to dark theme" : "Switch to light theme",
    );
    try {
      localStorage.setItem("stego-studio-theme", theme);
    } catch (_) {
      /* localStorage unavailable (e.g. private browsing) — theme just won't persist */
    }
  }

  function initTheme() {
    let saved = null;
    try {
      saved = localStorage.getItem("stego-studio-theme");
    } catch (_) {
      /* ignore */
    }
    applyTheme(saved === "light" || saved === "dark" ? saved : "dark");
  }

  themeToggle.addEventListener("click", () => {
    applyTheme(root.getAttribute("data-theme") === "dark" ? "light" : "dark");
  });

  /* ----------------------------------------------------------------
     8. TAB SWITCHING
     ---------------------------------------------------------------- */

  function activateTab(name) {
    const isHide = name === "hide";
    tabHide.setAttribute("aria-selected", String(isHide));
    tabReveal.setAttribute("aria-selected", String(!isHide));
    tabHide.tabIndex = isHide ? 0 : -1;
    tabReveal.tabIndex = isHide ? -1 : 0;
    panelHide.classList.toggle("hidden", !isHide);
    panelReveal.classList.toggle("hidden", isHide);
    tabIndicator.style.transform = isHide
      ? "translateX(0%)"
      : "translateX(100%)";
  }

  tabHide.addEventListener("click", () => activateTab("hide"));
  tabReveal.addEventListener("click", () => activateTab("reveal"));

  [tabHide, tabReveal].forEach((tab, idx, arr) => {
    tab.addEventListener("keydown", (e) => {
      if (e.key !== "ArrowRight" && e.key !== "ArrowLeft") return;
      e.preventDefault();
      const dir = e.key === "ArrowRight" ? 1 : -1;
      const next = arr[(idx + dir + arr.length) % arr.length];
      next.focus();
      next.click();
    });
  });

  /* ----------------------------------------------------------------
     9. TOAST NOTIFICATIONS
     ---------------------------------------------------------------- */

  const TOAST_ICONS = {
    success:
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"></circle><path d="M8.5 12.5l2.5 2.5 5-5.5"></path></svg>',
    error:
      '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3.5L21 19H3L12 3.5Z"></path><path d="M12 9.5v4.2"></path><path d="M12 16.8h.01"></path></svg>',
    info: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"></circle><path d="M12 11v5"></path><path d="M12 7.5h.01"></path></svg>',
  };
  const ICON_X =
    '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><path d="M6 6l12 12M18 6L6 18"></path></svg>';

  function showToast(type, title, message, duration = 5000) {
    const toast = document.createElement("div");
    toast.className = `toast toast--${type}`;
    toast.setAttribute("role", type === "error" ? "alert" : "status");

    const iconSpan = document.createElement("span");
    iconSpan.className = "toast-icon";
    iconSpan.innerHTML = TOAST_ICONS[type] || TOAST_ICONS.info;

    const content = document.createElement("div");
    content.className = "toast-content";
    const titleEl = document.createElement("p");
    titleEl.className = "toast-title";
    titleEl.textContent = title;
    const messageEl = document.createElement("p");
    messageEl.className = "toast-message";
    messageEl.textContent = message;
    content.append(titleEl, messageEl);

    const closeBtn = document.createElement("button");
    closeBtn.className = "toast-close";
    closeBtn.type = "button";
    closeBtn.setAttribute("aria-label", "Dismiss notification");
    closeBtn.innerHTML = ICON_X;

    const progress = document.createElement("span");
    progress.className = "toast-progress";
    progress.style.animationDuration = `${duration}ms`;

    toast.append(iconSpan, content, closeBtn, progress);
    toastContainer.appendChild(toast);

    let dismissTimer;
    const removeToast = () => {
      clearTimeout(dismissTimer);
      toast.classList.add("toast--leaving");
      setTimeout(() => toast.remove(), 260);
    };

    dismissTimer = setTimeout(removeToast, duration);
    closeBtn.addEventListener("click", removeToast);
    toast.addEventListener("mouseenter", () => clearTimeout(dismissTimer));
    toast.addEventListener("mouseleave", () => {
      dismissTimer = setTimeout(removeToast, 1500);
    });
  }

  function handleStegoError(err) {
    console.error(err);
    if (err instanceof StegoError) {
      let message = err.message;
      if (err.code === "CORRUPTED") {
        message =
          "The hidden data could not be recovered. The image was probably compressed too hard, resized or edited after sharing. If it was created in normal (non-WhatsApp-safe) mode, send it as a Document/File instead of a photo.";
      }
      showToast("error", ERROR_TITLES[err.code] || "Error", message);
    } else {
      showToast(
        "error",
        "Something went wrong",
        "An unexpected error occurred. Please try again.",
      );
    }
  }

  /* ----------------------------------------------------------------
     10. FILE LOADING & VALIDATION
     ---------------------------------------------------------------- */

  function validateImageFile(file) {
    if (!file) throw new StegoError("NO_FILE", "No file was selected.");
    const isImage =
      /^image\/(png|jpe?g|webp|gif|bmp)$/i.test(file.type) ||
      /\.(png|jpe?g|webp|gif|bmp)$/i.test(file.name);
    if (!isImage) {
      throw new StegoError(
        "INVALID_TYPE",
        "Please choose a PNG, JPG or WebP image.",
      );
    }
    if (file.size > MAX_FILE_SIZE) {
      throw new StegoError(
        "TOO_LARGE",
        "This image is larger than 25 MB. Please choose a smaller image.",
      );
    }
  }

  function loadImageFromFile(file) {
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onload = () => {
        const img = new Image();
        img.onload = () => resolve(img);
        img.onerror = () =>
          reject(
            new StegoError(
              "DECODE_FAILED",
              "This file could not be read as an image.",
            ),
          );
        img.src = reader.result;
      };
      reader.onerror = () =>
        reject(new StegoError("READ_FAILED", "The file could not be read."));
      reader.readAsDataURL(file);
    });
  }

  /** Draws an <img> onto an offscreen canvas at native resolution and returns its pixel data. */
  function imageToImageData(img) {
    const canvas = document.createElement("canvas");
    canvas.width = img.naturalWidth;
    canvas.height = img.naturalHeight;
    const ctx = canvas.getContext("2d", { willReadFrequently: true });
    ctx.drawImage(img, 0, 0);
    return ctx.getImageData(0, 0, canvas.width, canvas.height);
  }

  /** Size the image will have in robust mode (long side capped so WhatsApp won't resize it). */
  function robustDimensions(width, height) {
    const scale = Math.min(1, ROBUST_MAX_DIM / Math.max(width, height));
    return {
      width: Math.max(1, Math.round(width * scale)),
      height: Math.max(1, Math.round(height * scale)),
      scaled: scale < 1,
    };
  }

  /** Returns a copy of imageData scaled down to the robust-mode size (or the same data if small enough). */
  function fitImageDataForRobust(imageData) {
    const dims = robustDimensions(imageData.width, imageData.height);
    if (!dims.scaled) return imageData;
    const src = document.createElement("canvas");
    src.width = imageData.width;
    src.height = imageData.height;
    src.getContext("2d").putImageData(imageData, 0, 0);
    const dst = document.createElement("canvas");
    dst.width = dims.width;
    dst.height = dims.height;
    const ctx = dst.getContext("2d", { willReadFrequently: true });
    ctx.imageSmoothingEnabled = true;
    ctx.imageSmoothingQuality = "high";
    ctx.drawImage(src, 0, 0, dims.width, dims.height);
    return ctx.getImageData(0, 0, dims.width, dims.height);
  }

  function setButtonLoading(btn, isLoading, label) {
    btn.classList.toggle("is-loading", isLoading);
    btn.disabled = isLoading;
    btn.setAttribute("aria-busy", String(isLoading));
    if (label) btn.querySelector(".btn-text").textContent = label;
  }

  function downloadBlob(blob, filename) {
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function buildOutputFilename(originalName) {
    const base = (originalName || "image").replace(/\.(png|jpe?g|webp|gif|bmp)$/i, "");
    return `${base}-hidden.png`;
  }

  /* ----------------------------------------------------------------
     11. DRAG-AND-DROP WIRING
     ---------------------------------------------------------------- */

  function setupDropzone(dropzoneEl, inputEl, onFile) {
    const openPicker = () => inputEl.click();

    dropzoneEl.addEventListener("click", openPicker);
    dropzoneEl.addEventListener("keydown", (e) => {
      if (e.key === "Enter" || e.key === " ") {
        e.preventDefault();
        openPicker();
      }
    });

    ["dragenter", "dragover"].forEach((evt) =>
      dropzoneEl.addEventListener(evt, (e) => {
        e.preventDefault();
        e.stopPropagation();
        dropzoneEl.classList.add("dropzone--active");
      }),
    );
    ["dragleave", "drop"].forEach((evt) =>
      dropzoneEl.addEventListener(evt, (e) => {
        e.preventDefault();
        e.stopPropagation();
        dropzoneEl.classList.remove("dropzone--active");
      }),
    );
    dropzoneEl.addEventListener("drop", (e) => {
      const file = e.dataTransfer.files && e.dataTransfer.files[0];
      if (file) onFile(file);
    });

    inputEl.addEventListener("change", (e) => {
      const file = e.target.files && e.target.files[0];
      if (file) onFile(file);
      inputEl.value = ""; // allow re-selecting the same file later
    });
  }

  function setupPasswordVisibilityToggle(button, input) {
    button.addEventListener("click", () => {
      const showing = input.type === "text";
      input.type = showing ? "password" : "text";
      button.classList.toggle("is-active", !showing);
      button.setAttribute(
        "aria-label",
        showing ? "Show password" : "Hide password",
      );
    });
  }

  /* ----------------------------------------------------------------
     12. "HIDE MESSAGE" TAB WIRING
     ---------------------------------------------------------------- */

  async function handleHideFile(file) {
    try {
      validateImageFile(file);
      hideDropzone.classList.add("is-loading");

      const img = await loadImageFromFile(file);
      const imageData = imageToImageData(img);

      state.hide.file = file;
      state.hide.fileName = file.name;
      state.hide.imageData = imageData;

      hidePreviewImg.src = URL.createObjectURL(file);
      hidePreviewWrap.classList.remove("hidden");
      hideDropzone.classList.add("hidden");
      hideImgDims.textContent = `${imageData.width} × ${imageData.height} px`;
      hideImgSize.textContent = formatBytes(file.size);

      recalcHideCapacity();
      showToast(
        "success",
        "Image loaded",
        `${file.name} is ready — you can now type your message.`,
      );
    } catch (err) {
      handleStegoError(err);
    } finally {
      hideDropzone.classList.remove("is-loading");
    }
  }

  function resetHideImage() {
    state.hide.file = null;
    state.hide.fileName = "";
    state.hide.imageData = null;
    state.hide.capacityBytes = 0;
    hidePreviewWrap.classList.add("hidden");
    hideDropzone.classList.remove("hidden");
    hidePreviewImg.src = "";
    recalcHideCapacity();
  }

  function recalcHideCapacity() {
    const message = hideMessageInput.value;
    const charCount = message.length;
    const byteCount = new TextEncoder().encode(message).length;

    hideCharCount.textContent = `${charCount} character${charCount === 1 ? "" : "s"}`;

    const useEncryption = hideEncryptToggle.checked;
    const overhead = useEncryption
      ? SALT_LENGTH + IV_LENGTH + GCM_TAG_LENGTH
      : 0;
    const totalNeeded = byteCount + overhead;
    hideByteCount.textContent = `${formatBytes(totalNeeded)} to embed`;

    const hasImage = !!state.hide.imageData;
    if (!hasImage) {
      hideCapacityFill.style.width = "0%";
      hideCapacityFill.classList.remove("capacity-bar-fill--over");
      hideCapacityTrack.setAttribute("aria-valuenow", "0");
      hideCapacityHint.textContent =
        "Upload an image to see how much you can hide.";
      hideCapacityHint.classList.remove("hint-text--warn");
      hideSubmitBtn.disabled = true;
      return;
    }

    let capacity;
    if (hideRobustToggle.checked) {
      const d = robustDimensions(
        state.hide.imageData.width,
        state.hide.imageData.height,
      );
      capacity = robustCapacityBytes(d.width, d.height);
    } else {
      capacity = Math.max(
        0,
        Math.floor(usableChannelCount(state.hide.imageData) / 8) - HEADER_BYTES,
      );
    }
    state.hide.capacityBytes = capacity;
    const percent =
      capacity > 0 ? Math.min(100, (totalNeeded / capacity) * 100) : 100;
    const fits = capacity > 0 && totalNeeded <= capacity;

    hideCapacityFill.style.width = `${percent}%`;
    hideCapacityFill.classList.toggle("capacity-bar-fill--over", !fits);
    hideCapacityTrack.setAttribute(
      "aria-valuenow",
      String(Math.round(percent)),
    );

    hideCapacityHint.textContent = fits
      ? `${formatBytes(totalNeeded)} of ${formatBytes(capacity)} capacity used.`
      : `Message exceeds this image's capacity of ${formatBytes(capacity)}. Try a larger image or a shorter message.`;
    hideCapacityHint.classList.toggle("hint-text--warn", !fits);

    const passwordOk = !useEncryption || hidePasswordInput.value.length > 0;
    hideSubmitBtn.disabled = !(fits && byteCount > 0 && passwordOk);
  }

  async function runHideFlow() {
    try {
      if (!state.hide.imageData)
        throw new StegoError("NO_IMAGE", "Please upload an image first.");

      const message = hideMessageInput.value;
      if (!message.trim())
        throw new StegoError(
          "EMPTY_MESSAGE",
          "Please enter a message to hide.",
        );

      const useEncryption = hideEncryptToggle.checked;
      const password = useEncryption ? hidePasswordInput.value : null;
      if (useEncryption && !password) {
        throw new StegoError(
          "NO_PASSWORD",
          "Please enter a password, or turn off encryption.",
        );
      }

      setButtonLoading(hideSubmitBtn, true, "Encoding pixels…");

      const robust = hideRobustToggle.checked;

      // Work on a clone so a second attempt never compounds onto already-modified data.
      // In robust mode the image is first shrunk to a size WhatsApp will not resize again.
      const sourceData = robust
        ? fitImageDataForRobust(state.hide.imageData)
        : state.hide.imageData;
      const working = new ImageData(
        new Uint8ClampedArray(sourceData.data),
        sourceData.width,
        sourceData.height,
      );

      await encodeMessageIntoImageData(working, message, password, robust);
      await wait(350); // keeps the loading state perceivable, even on tiny images

      setButtonLoading(hideSubmitBtn, true, "Preparing PNG…");
      const outCanvas = document.createElement("canvas");
      outCanvas.width = working.width;
      outCanvas.height = working.height;
      outCanvas.getContext("2d").putImageData(working, 0, 0);

      outCanvas.toBlob((blob) => {
        if (!blob) {
          handleStegoError(
            new StegoError(
              "DECODE_FAILED",
              "The image could not be generated. Please try again.",
            ),
          );
          setButtonLoading(hideSubmitBtn, false, "Create Hidden Image");
          return;
        }
        downloadBlob(blob, buildOutputFilename(state.hide.fileName));
        setButtonLoading(hideSubmitBtn, true, "Downloaded ✓");
        showToast(
          "success",
          "Hidden image created",
          robust
            ? `Saved as ${working.width} × ${working.height} px PNG. Send it as a normal photo on WhatsApp — the message will survive.`
            : "Your image downloaded with the secret message embedded inside it. Send it as a file/document (not a photo) so it is not compressed.",
        );
        setTimeout(() => {
          setButtonLoading(hideSubmitBtn, false, "Create Hidden Image");
          recalcHideCapacity();
        }, 1100);
      }, "image/png");
    } catch (err) {
      handleStegoError(err);
      setButtonLoading(hideSubmitBtn, false, "Create Hidden Image");
      recalcHideCapacity();
    }
  }

  function initHideTab() {
    setupDropzone(hideDropzone, hideFileInput, handleHideFile);
    hideRemoveImg.addEventListener("click", resetHideImage);
    hideMessageInput.addEventListener("input", recalcHideCapacity);

    hideRobustToggle.addEventListener("change", recalcHideCapacity);

    hideEncryptToggle.addEventListener("change", () => {
      hidePasswordWrap.classList.toggle("hidden", !hideEncryptToggle.checked);
      recalcHideCapacity();
    });
    hidePasswordInput.addEventListener("input", recalcHideCapacity);
    setupPasswordVisibilityToggle(hidePasswordVisibility, hidePasswordInput);

    if (!hasWebCrypto) {
      hideEncryptToggle.disabled = true;
      hideEncryptToggle.closest(".toggle-row").title =
        "Password encryption needs the Web Crypto API, which is not available in this browser.";
    }

    hideSubmitBtn.addEventListener("click", runHideFlow);
    recalcHideCapacity();
  }

  /* ----------------------------------------------------------------
     13. "REVEAL MESSAGE" TAB WIRING
     ---------------------------------------------------------------- */

  async function handleRevealFile(file) {
    try {
      validateImageFile(file);
      revealDropzone.classList.add("is-loading");

      const img = await loadImageFromFile(file);
      const imageData = imageToImageData(img);

      state.reveal.file = file;
      state.reveal.imageData = imageData;

      revealPreviewImg.src = URL.createObjectURL(file);
      revealPreviewWrap.classList.remove("hidden");
      revealDropzone.classList.add("hidden");
      revealImgDims.textContent = `${imageData.width} × ${imageData.height} px`;
      revealImgSize.textContent = formatBytes(file.size);

      revealOutputWrap.classList.add("hidden");
      revealSubmitBtn.disabled = false;

      showToast("success", "Image loaded", `${file.name} is ready to decode.`);
    } catch (err) {
      handleStegoError(err);
    } finally {
      revealDropzone.classList.remove("is-loading");
    }
  }

  function resetRevealImage() {
    state.reveal.file = null;
    state.reveal.imageData = null;
    state.reveal.lastMessage = "";
    revealPreviewWrap.classList.add("hidden");
    revealDropzone.classList.remove("hidden");
    revealPreviewImg.src = "";
    revealOutputWrap.classList.add("hidden");
    revealSubmitBtn.disabled = true;
  }

  /** Types the decoded message out while a neon scanline sweeps the terminal — the app's signature moment. */
  async function typewriterReveal(text) {
    revealOutputWrap.classList.remove("hidden");
    revealOutputText.textContent = "";

    if (prefersReducedMotion || text.length === 0) {
      revealOutputText.textContent = text;
      return;
    }

    revealOutputWrap.classList.add("scanning");
    const chars = Array.from(text); // iterate by Unicode code point, not UTF-16 unit
    const perCharDelay = chars.length > 400 ? 4 : chars.length > 150 ? 9 : 16;

    for (let i = 0; i < chars.length; i++) {
      revealOutputText.textContent += chars[i];
      if (i % 2 === 0) await wait(perCharDelay);
    }
    revealOutputWrap.classList.remove("scanning");
  }

  async function runRevealFlow() {
    try {
      if (!state.reveal.imageData)
        throw new StegoError("NO_IMAGE", "Please upload an image first.");

      setButtonLoading(revealSubmitBtn, true, "Scanning pixels…");
      await wait(300);

      const password = revealPasswordInput.value || null;
      if (password) setButtonLoading(revealSubmitBtn, true, "Decrypting…");

      const message = await decodeMessageFromImageData(
        state.reveal.imageData,
        password,
      );
      state.reveal.lastMessage = message;

      await typewriterReveal(message);
      showToast(
        "success",
        "Message revealed",
        "The hidden message was decoded successfully.",
      );
    } catch (err) {
      revealOutputWrap.classList.add("hidden");
      handleStegoError(err);
      if (err instanceof StegoError && err.code === "PASSWORD_REQUIRED") {
        revealPasswordInput.focus();
      }
    } finally {
      setButtonLoading(revealSubmitBtn, false, "Reveal Message");
    }
  }

  async function copyRevealedMessage() {
    const text = state.reveal.lastMessage || "";
    try {
      await navigator.clipboard.writeText(text);
      showToast(
        "success",
        "Copied",
        "The message was copied to your clipboard.",
      );
    } catch (_) {
      // Fallback for browsers/contexts without Clipboard API permission
      try {
        const range = document.createRange();
        range.selectNodeContents(revealOutputText);
        const selection = window.getSelection();
        selection.removeAllRanges();
        selection.addRange(range);
        showToast(
          "info",
          "Copy manually",
          "Clipboard access was blocked — the text is selected, press Ctrl/Cmd+C.",
        );
      } catch (_) {
        showToast(
          "error",
          "Copy failed",
          "Could not access the clipboard in this browser.",
        );
      }
    }
  }

  function initRevealTab() {
    setupDropzone(revealDropzone, revealFileInput, handleRevealFile);
    revealRemoveImg.addEventListener("click", resetRevealImage);
    setupPasswordVisibilityToggle(
      revealPasswordVisibility,
      revealPasswordInput,
    );
    revealSubmitBtn.addEventListener("click", runRevealFlow);
    revealCopyBtn.addEventListener("click", copyRevealedMessage);
  }

  /* ----------------------------------------------------------------
     14. BOOT
     ---------------------------------------------------------------- */

  initTheme();
  initHideTab();
  initRevealTab();
})();
