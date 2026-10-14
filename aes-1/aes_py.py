# aes_py.py
# AES-128 实现（FIPS-197）

# S 盒
SBOX = [
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16,
]

# 逆 S 盒，由 S 盒反查生成，防止手抄出错
INV_SBOX = [0] * 256
for _i, _v in enumerate(SBOX):
    INV_SBOX[_v] = _i

# 轮常量，第 0 位不用
RCON = (0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36)


def _gmul(a, b):
    """GF(2^8) 乘法，模不可约多项式 0x11B"""
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1B
        b >>= 1
    return p


# 列混合用到的 2x / 3x 查找表
MUL2 = tuple(_gmul(i, 0x02) for i in range(256))
MUL3 = tuple(_gmul(i, 0x03) for i in range(256))


def key_expand(key):
    """密钥扩展：16 字节密钥 -> 44 个字，每字 4 字节"""
    if len(key) != 16:
        raise ValueError("key must be 16 bytes")
    w = [list(key[4 * i:4 * i + 4]) for i in range(4)]
    for i in range(4, 44):
        t = w[i - 1][:]
        if i % 4 == 0:
            t = t[1:] + t[:1]           # RotWord
            t = [SBOX[b] for b in t]    # SubWord
            t[0] ^= RCON[i // 4]        # 异或轮常量
        w.append([w[i - 4][j] ^ t[j] for j in range(4)])
    return w


def add_round_key(state, w, rnd):
    """轮密钥加。state 按列优先存放：state[c*4 + r]"""
    for c in range(4):
        word = w[rnd * 4 + c]
        for r in range(4):
            state[c * 4 + r] ^= word[r]


def sub_bytes(state):
    """字节代换"""
    for i in range(16):
        state[i] = SBOX[state[i]]


def inv_sub_bytes(state):
    """逆字节代换"""
    for i in range(16):
        state[i] = INV_SBOX[state[i]]


def shift_rows(state):
    """行移位：第 r 行循环左移 r 个字节"""
    # 第 1 行左移 1
    t = state[1]; state[1] = state[5]; state[5] = state[9]; state[9] = state[13]; state[13] = t
    # 第 2 行左移 2
    t = state[2]; state[2] = state[10]; state[10] = t
    t = state[6]; state[6] = state[14]; state[14] = t
    # 第 3 行左移 3，等价右移 1
    t = state[15]; state[15] = state[11]; state[11] = state[7]; state[7] = state[3]; state[3] = t


def inv_shift_rows(state):
    """逆行移位：第 r 行循环右移 r 个字节"""
    # 第 1 行右移 1
    t = state[13]; state[13] = state[9]; state[9] = state[5]; state[5] = state[1]; state[1] = t
    # 第 2 行右移 2
    t = state[2]; state[2] = state[10]; state[10] = t
    t = state[6]; state[6] = state[14]; state[14] = t
    # 第 3 行右移 3，等价左移 1
    t = state[3]; state[3] = state[7]; state[7] = state[11]; state[11] = state[15]; state[15] = t


def mix_columns(state):
    """列混合，每列左乘固定矩阵"""
    for c in range(4):
        a0 = state[c * 4 + 0]; a1 = state[c * 4 + 1]
        a2 = state[c * 4 + 2]; a3 = state[c * 4 + 3]
        state[c * 4 + 0] = MUL2[a0] ^ MUL3[a1] ^ a2 ^ a3
        state[c * 4 + 1] = a0 ^ MUL2[a1] ^ MUL3[a2] ^ a3
        state[c * 4 + 2] = a0 ^ a1 ^ MUL2[a2] ^ MUL3[a3]
        state[c * 4 + 3] = MUL3[a0] ^ a1 ^ a2 ^ MUL2[a3]


def inv_mix_columns(state):
    """逆列混合"""
    for c in range(4):
        a0 = state[c * 4 + 0]; a1 = state[c * 4 + 1]
        a2 = state[c * 4 + 2]; a3 = state[c * 4 + 3]
        state[c * 4 + 0] = _gmul(a0, 0x0e) ^ _gmul(a1, 0x0b) ^ _gmul(a2, 0x0d) ^ _gmul(a3, 0x09)
        state[c * 4 + 1] = _gmul(a0, 0x09) ^ _gmul(a1, 0x0e) ^ _gmul(a2, 0x0b) ^ _gmul(a3, 0x0d)
        state[c * 4 + 2] = _gmul(a0, 0x0d) ^ _gmul(a1, 0x09) ^ _gmul(a2, 0x0e) ^ _gmul(a3, 0x0b)
        state[c * 4 + 3] = _gmul(a0, 0x0b) ^ _gmul(a1, 0x0d) ^ _gmul(a2, 0x09) ^ _gmul(a3, 0x0e)


def aes128_encrypt_block(key, block):
    """AES-128 加密单个 16 字节分组"""
    if len(block) != 16:
        raise ValueError("block must be 16 bytes")
    w = key_expand(key)
    st = list(block)

    add_round_key(st, w, 0)
    # 第 1~9 轮
    for rnd in range(1, 10):
        sub_bytes(st)
        shift_rows(st)
        mix_columns(st)
        add_round_key(st, w, rnd)
    # 第 10 轮不含列混合
    sub_bytes(st)
    shift_rows(st)
    add_round_key(st, w, 10)
    return bytes(st)


def aes128_decrypt_block(key, block):
    """AES-128 解密单个 16 字节分组，轮变换顺序与加密相反"""
    if len(block) != 16:
        raise ValueError("block must be 16 bytes")
    w = key_expand(key)
    st = list(block)

    add_round_key(st, w, 10)
    for rnd in range(9, 0, -1):
        inv_shift_rows(st)
        inv_sub_bytes(st)
        add_round_key(st, w, rnd)
        inv_mix_columns(st)
    inv_shift_rows(st)
    inv_sub_bytes(st)
    add_round_key(st, w, 0)
    return bytes(st)


def main():
    # FIPS-197 附录 B 测试向量
    key = bytes(range(16))                                     # 000102...0f
    pt = bytes.fromhex("00112233445566778899aabbccddeeff")
    want = bytes.fromhex("69c4e0d86a7b0430d8cdb78070b4c55a")

    ct = aes128_encrypt_block(key, pt)
    dec = aes128_decrypt_block(key, ct)

    print("key       ", key.hex())
    print("plain     ", pt.hex())
    print("cipher    ", ct.hex())
    print("expected  ", want.hex())
    print("decrypt   ", dec.hex())
    print("encrypt", "OK" if ct == want else "FAIL")
    print("decrypt", "OK" if dec == pt else "FAIL")


if __name__ == "__main__":
    main()