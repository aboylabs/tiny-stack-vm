// Tiny stack VM for make.fun's ISA v1: runs each program in the input
// directory, writes stdout.bin + exit.txt per instance to the output directory.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Traps: 2 underflow, 3 overflow, 4 div by zero, 5 bad opcode, 6 bad address,
// 7 call depth, 8 empty return, 9 bad pc, 10 step limit, 11 output limit.
function run(prog, feed) {
  const st = new Int32Array(256);
  const rt = new Int32Array(64);
  const mm = new Int32Array(256);
  const op = new Uint8Array(65536);
  let sp = 0, rp = 0, pc = 0, ip = 0, ol = 0, steps = 0, code = 0;
  const n = prog.length;
  outer: for (;;) {
    if (steps >= 1000000) { code = 10; break; }
    if (pc < 0 || pc >= n) { code = 9; break; }
    const b = prog[pc];
    const il = b === 1 ? 1 : b === 2 ? 4 : b >= 0x30 && b <= 0x33 ? 2 : 0;
    if (pc + il >= n) { code = 9; break; }
    steps++;
    const nx = pc + 1 + il;
    pc = nx;
    switch (b) {
      case 0x00:
        code = 0;
        break outer;
      case 0x01:
        if (sp > 255) { code = 3; break outer; }
        st[sp++] = (prog[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        if (sp > 255) { code = 3; break outer; }
        st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03:
        if (sp < 1) { code = 2; break outer; }
        sp--;
        break;
      case 0x04:
        if (sp < 1) { code = 2; break outer; }
        if (sp > 255) { code = 3; break outer; }
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 0x05:
        if (sp < 2) { code = 2; break outer; }
        { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }
        break;
      case 0x06:
        if (sp < 2) { code = 2; break outer; }
        if (sp > 255) { code = 3; break outer; }
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 0x07:
        if (sp < 3) { code = 2; break outer; }
        { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; }
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) { code = 2; break outer; }
        const y = st[sp - 1], x = st[sp - 2];
        let r;
        if (b === 0x15) {
          if (y === 0) { code = 4; break outer; }
          r = Math.floor((x >>> 0) / (y >>> 0)) | 0;
        } else if (b === 0x16) {
          if (y === 0) { code = 4; break outer; }
          r = ((x >>> 0) % (y >>> 0)) | 0;
        } else if (b === 0x22) {
          r = (x >>> 0) < (y >>> 0) ? 1 : 0;
        } else if (b === 0x13) {
          if (y === 0) { code = 4; break outer; }
          r = (x === -2147483648 && y === -1) ? x : (x / y) | 0;
        } else if (b === 0x14) {
          if (y === 0) { code = 4; break outer; }
          r = y === -1 ? 0 : (x % y) | 0;
        } else if (b === 0x12) r = Math.imul(x, y);
        else if (b === 0x10) r = (x + y) | 0;
        else if (b === 0x11) r = (x - y) | 0;
        else if (b === 0x1c) r = x << (y & 31);
        else if (b === 0x1d) r = x >> (y & 31);
        else if (b === 0x1e) r = (x >>> (y & 31)) | 0;
        else if (b === 0x18) r = x & y;
        else if (b === 0x19) r = x | y;
        else if (b === 0x1a) r = x ^ y;
        else if (b === 0x20) r = x === y ? 1 : 0;
        else r = x < y ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x17:
        if (sp < 1) { code = 2; break outer; }
        st[sp - 1] = (-st[sp - 1]) | 0;
        break;
      case 0x1b:
        if (sp < 1) { code = 2; break outer; }
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x30:
        pc = nx + (((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16);
        break;
      case 0x31: case 0x32: {
        if (sp < 1) { code = 2; break outer; }
        const v = st[--sp];
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        if (b === 0x31 ? v === 0 : v !== 0) pc = nx + rel;
        break;
      }
      case 0x33:
        if (rp === 64) { code = 7; break outer; }
        rt[rp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (rp === 0) { code = 8; break outer; }
        pc = rt[--rp];
        break;
      case 0x40: {
        if (sp < 1) { code = 2; break outer; }
        const a = st[sp - 1];
        if (a < 0 || a > 255) { code = 6; break outer; }
        st[sp - 1] = mm[a];
        break;
      }
      case 0x41: {
        if (sp < 2) { code = 2; break outer; }
        const a = st[sp - 1];
        if (a < 0 || a > 255) { code = 6; break outer; }
        mm[a] = st[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        if (sp < 1) { code = 2; break outer; }
        const s = String(st[sp - 1]);
        if (ol + s.length > 65536) { code = 11; break outer; }
        sp--;
        for (let i = 0; i < s.length; i++) op[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (sp < 1) { code = 2; break outer; }
        if (ol >= 65536) { code = 11; break outer; }
        op[ol++] = st[--sp] & 255;
        break;
      case 0x52:
        if (sp > 255) { code = 3; break outer; }
        st[sp++] = ip < feed.length ? feed[ip++] : -1;
        break;
      case 0x53:
        if (sp < 1) { code = 2; break outer; }
        code = st[--sp] & 255;
        break outer;
      default:
        code = 5;
        break outer;
    }
  }
  return { bytes: op.slice(0, ol), code };
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
