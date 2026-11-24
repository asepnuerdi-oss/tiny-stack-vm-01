// Tiny stack VM, make.fun tiny stack ISA v1: a correct interpreter.
// Wrapping 32-bit math, unsigned ops, masked shifts, every trap code,
// step and output limits. Small matters: score ties break by size.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
function run(p, q) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (c) => [out.subarray(0, olen), c];
  for (;;) {
    if (steps >= 1e6) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const at = pc, op = p[at];
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    const ok = op <= 7 || (op >= 0x10 && op <= 0x22 && op !== 0x1f) ||
      (op >= 0x30 && op <= 0x34) || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
    if (!ok) return end(5);
    if (imm && at + imm >= p.length) return end(9);
    steps++;
    pc = at + 1 + imm;
    switch (op) {
      case 0x00: return end(0);
      case 0x01:
        if (sp >= 256) return end(3);
        D[sp++] = (p[at + 1] << 24) >> 24; break;
      case 0x02:
        if (sp >= 256) return end(3);
        D[sp++] = p[at + 1] | (p[at + 2] << 8) | (p[at + 3] << 16) | (p[at + 4] << 24); break;
      case 0x03: if (sp < 1) return end(2); sp--; break;
      case 0x04:
        if (sp < 1) return end(2);
        if (sp >= 256) return end(3);
        D[sp] = D[sp - 1]; sp++; break;
      case 0x05: {
        if (sp < 2) return end(2);
        const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break;
      }
      case 0x06:
        if (sp < 2) return end(2);
        if (sp >= 256) return end(3);
        D[sp] = D[sp - 2]; sp++; break;
      case 0x07: {
        if (sp < 3) return end(2);
        const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break;
      }
      case 0x17: if (sp < 1) return end(2); D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: if (sp < 1) return end(2); D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[at + 1] | (p[at + 2] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) {
          if (sp < 1) return end(2);
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc += rel;
        break;
      }
      case 0x33:
        if (csp >= 64) return end(7);
        C[csp++] = pc; pc = p[at + 1] | (p[at + 2] << 8); break;
      case 0x34: if (csp < 1) return end(8); pc = C[--csp]; break;
      case 0x40: {
        if (sp < 1) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a]; break;
      }
      case 0x41: {
        if (sp < 2) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2]; sp -= 2; break;
      }
      case 0x50: {
        if (sp < 1) return end(2);
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (sp < 1) return end(2);
        if (olen >= 65536) return end(11);
        out[olen++] = D[--sp] & 255; break;
      case 0x52:
        if (sp >= 256) return end(3);
        D[sp++] = ip < q.length ? q[ip++] : -1; break;
      case 0x53:
        if (sp < 1) return end(2);
        return end(D[--sp] & 255);
      default: {
        if (sp < 2) return end(2);
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (!b) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        D[sp - 2] = r; sp--; break;
      }
    }
  }
}
for (const id of readdirSync(I).sort()) {
  let inp;
  try { inp = readFileSync(join(I, id, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const [bytes, code] = run(readFileSync(join(I, id, 'program.bin')), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), bytes);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
