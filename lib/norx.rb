class Norx

  attr_reader :w, :r, :d, :t

  def initialize(w = 64, r = 4, d = 1, t = 256)
    @w = w
    @r = r
    @d = d
    @t = t
    raise unless valid_params?
  end

  def _load(x)
    x.unpack(vars[:fmt]).first
  end

  def store(x)
    if x.is_a?(Array)
      x.pack(vars[:fmt])
    else
      [x].pack(vars[:fmt])
    end
  end

  def rotr(a, r)
    ((a >> r) | (a << (vars[:NORX_W] - r))) & vars[:M]
  end

  def h(a, b)
    ((a ^ b) ^ ((a & b) << 1)) & vars[:M]
  end

  def g(a, b, c, d)
    a = h(a, b)
    d = rotr(a ^ d, vars[:R][0])
    c = h(c, d)
    b = rotr(b ^ c, vars[:R][1])
    a = h(a, b)
    d = rotr(a ^ d, vars[:R][2])
    c = h(c, d)
    b = rotr(b ^ c, vars[:R][3])
    [a, b, c, d]
  end

  def f(s)
    # Column step
    s[ 0], s[ 4], s[ 8], s[12] = g(s[ 0], s[ 4], s[ 8], s[12]);
    s[ 1], s[ 5], s[ 9], s[13] = g(s[ 1], s[ 5], s[ 9], s[13]);
    s[ 2], s[ 6], s[10], s[14] = g(s[ 2], s[ 6], s[10], s[14]);
    s[ 3], s[ 7], s[11], s[15] = g(s[ 3], s[ 7], s[11], s[15]);
    # Diagonal step
    s[ 0], s[ 5], s[10], s[15] = g(s[ 0], s[ 5], s[10], s[15]);
    s[ 1], s[ 6], s[11], s[12] = g(s[ 1], s[ 6], s[11], s[12]);
    s[ 2], s[ 7], s[ 8], s[13] = g(s[ 2], s[ 7], s[ 8], s[13]);
    s[ 3], s[ 4], s[ 9], s[14] = g(s[ 3], s[ 4], s[ 9], s[14]);
    s
  end

  def permute(s)
    vars[:NORX_R].times do
      s = f(s)
    end
    s
  end

  def pad(self,x):
    y = bytearray(self.BYTES_RATE)
    x.length.times do |i|
      y[i-1] = x
    end
    y[x.length] = 0x01
    y[vars[:BYTES_RATE]-1] |= 0x80 # TODO
    y
  end

  def init(s, n, k)
    b = vars[:BYTES_WORD]
    (vars[:NORX_K] / vars[:NORX_W]).times do |i|
      k = [ _load(k[b*i..b*(i+1)]) for i in xrange(self.NORX_K / self.NORX_W) ]
    end
    (vars[:NORX_N] / vars[:NORX_W]).times do |i|
      n = [ _load(n[b*i..b*(i+1)])
    end
    u = vars[:U]
    s[ 0], s[ 1], s[ 2], s[ 3] = u[0], n[0], n[1], u[1]
    s[ 4], s[ 5], s[ 6], s[ 7] = k[0], k[1], k[2], k[3]
    s[ 8], s[ 9], s[10], s[11] = u[2], u[3], u[4], u[5]
    s[12], s[13], s[14], s[15] = u[6], u[7], u[8], u[9]
    s[12] ^= vars[:NORX_W]
    s[13] ^= vars[:NORX_R]
    s[14] ^= vars[:NORX_D]
    s[15] ^= vars[:NORX_T]
    permute(s)
  end

  def inject_tag(s, tag)
    s[15] ^= tag
  end

  def process_header(s, x)
    absorb_data(s, x, vars[:HEADER_TAG])
  end

  def process_trailer(s, x)
    absorb_data(s, x, vars[:TRAILER_TAG])
  end

  def absorb_data(s, x, tag)
    inlen = x.length
    if inlen > 0
      i, n = 0, vars[:BYTES_RATE]
      while inlen >= n
        absorb_block(s, x[n*i..n*(i+1)], tag)
        inlen -= n
        i += 1
      end
      absorb_lastblock(s, x[n*i..(n*i+inlen)], tag)
    end
  end

  def absorb_block(s, x, tag)
    b = vars[:BYTES_WORD]
    inject_tag(s, tag)
    permute(s)
    vars[:WORDS_RATE].times do |i|
      s[i] ^= _load(x[b*i..b*(i+1)])
    end
  end

  def absorb_lastblock(s, x, tag)
    y = pad(x)
    absorb_block(s, y, tag)
  end

  def encrypt_data(s, x)
    c = []
    inlen = x.length
    if inlen > 0
      i, n = 0, vars[:BYTES_RATE]
      while inlen >= n
        c += encrypt_block(s,x[n*i..n*(i+1)])
        inlen -= n
        i += 1
      end
      c += encrypt_lastblock(s, x[n*i..(n*i+inlen)])
    end
    c
  end

  def encrypt_block(s, x)
    c = []
    b = vars[:BYTES_WORD]
    inject_tag(s, vars[:PAYLOAD_TAG])
    permute(s)
    vars[:WORDS_RATE].times do |i|
      s[i] ^= _load(x[b*i..b*(i+1)])
      c += store(s[i])
    end
    c[0..vars[:BYTES_RATE]]
  end

  def encrypt_lastblock(s, x)
    y = pad(x)
    c = encrypt_block(s, y)
    c[0..x.length]
  end

  def decrypt_data(s, x)
    m = []
    inlen = x.length
    if inlen > 0
      i, n = 0, vars[:BYTES_RATE]
      while inlen >= n
        m += decrypt_block(s, x[n*i..n*(i+1)])
        inlen -= n
        i +=1
      end
      m += decrypt_lastblock(s, x[n*i..(n*i+inlen)])
    end
    m
  end

  def decrypt_block(s, x)
    m = []
    b = vars[:BYTES_WORD]
    inject_tag(s, vars[:PAYLOAD_TAG])
    permute(s)
    vars[:WORDS_RATE].times do |i|
      c = _load(x[b*i..b*(i+1)])
      m += store(s[i] ^ c)
      s[i] = c
    end
    m[0..vars[:BYTES_RATE]]
  end

  def decrypt_lastblock(s, x)
    m = []
    y = []
    b = vars[:BYTES_WORD]
    inject_tag(s, vars[:PAYLOAD_TAG])
    permute(s)
    vars[:WORDS_RATE].times do |i|
      y += store(s[i])
    end
    y[0..x.length] = Array.new(x)
    y[x.length] ^= 0x01
    y[vars[:BYTES_RATE-1]] ^= 0x80
    vars[:WORDS_RATE].times do |i|
      c = _load(y[b*i..b*(i+1)])
      m += store(s[i] ^ c)
      s[i] = c
    end
    m[0..x.length]
  end

  def generate_tag(s)
    t = []
    inject_tag(s, vars[:FINAL_TAG])
    permute(s)
    permute(s)
    vars[:WORDS_RATE].times do |i|
      t += store(s[i])
    end
    t[0..vars[:BYTES_TAG]]
  end

  def verify_tag(t0, t1)
    acc = 0
    vars[:BYTES_TAG].times do |i|
      acc |= t0[i] ^ t1[i]
    end
    (((acc - 1) >> 8) & 1) - 1
  end

  def aead_encrypt(h, m, t, n, k)
    raise unless k.length == vars[:NORX_K] / 8
    raise unless n.length == vars[:NORX_N] / 8
    c = []
    s = [0] * 16
    init(s, n, k)
    process_header(s, h)
    c += encrypt_data(s, m)
    process_trailer(s, t)
    c += generate_tag(s)
    c.to_s
  end

  def aead_decrypt(h, c, t, n, k)
    raise unless k.length == vars[:NORX_K] / 8
    raise unless n.length == vars[:NORX_N] / 8
    raise unless c.length >= vars[:BYTES_TAG] / 8
    m = []
    c = []
    s = [0] * 16
    d = c.length - vars[:BYTES_TAG]
    c = c[0..d]
    t0 = c[d..-1]
    init(s, n, k)
    process_header(s, h)
    m += decrypt_data(s, c)
    process_trailer(s, t)
    t1 = generate_tag(s)
    if verify_tag(t0, t1) != 0
      m = ''
    end
    m.to_s
  end

  private

  def vars
    @vars ||= begin
      _vars = \
        {
          :NORX_W => w,
          :NORX_R => r,
          :NORX_D => d,
          :NORX_T => t,
          :NORX_N => w * 2,
          :NORX_K => w * 4,
          :NORX_B => w * 16,
          :NORX_C => w * 6,
          :HEADER_TAG  =>  1 << 0,
          :PAYLOAD_TAG => 1 << 1,
          :TRAILER_TAG => 1 << 2,
          :FINAL_TAG   =>   1 << 3,
          :BRANCH_TAG  =>  1 << 4,
          :MERGE_TAG   =>   1 << 5,
          :BYTES_WORD  => w / 8,
          :BYTES_TAG   => t / 8,
        }
      _vars[:RATE]       = _vars[:NORX_B] - _vars[:NORX_C]
      _vars[:WORDS_RATE] = _vars[:RATE] / w
      _vars[:BYTES_RATE] = _vars[:WORDS_RATE] * _vars[:BYTES_WORD]
      if w == 32
        _vars[:R]   = (8,11,16,31)
        _vars[:U]   = (0x243F6A88, 0x85A308D3, 0x13198A2E, 0x03707344, 0x254F537A,
                       0x38531D48, 0x839C6E83, 0xF97A3AE5, 0x8C91D88C, 0x11EAFB59)
        _vars[:M]   = 0xffffffff
        _vars[:fmt] = '<L'
      else
        _vars[:R]   = (8,19,40,63)
        _vars[:U]   = (0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0, 0x082EFA98EC4E6C89, 0xAE8858DC339325A1,
                       0x670A134EE52D7FA6, 0xC4316D80CD967541, 0xD21DFBF8B630B762, 0x375A18D261E7F892, 0x343D1F187D92285B)
        _vars[:M]   = 0xffffffffffffffff
        _vars[:fmt] = '<Q'
      end
    end
  end

  def valid_params?
    [32,64].include?(w) &&
    r >= 1 &&
    d >= 0 &&
    10*w >= t && t >= 0
  end

end
