# Multiplication by squared addition with optimal evaluation

# Bits (Scott)
type Bits = E | (O (p: Bits)) | (I (p: Bits))
o = Bits/O
i = Bits/I
e = Bits/E

# Squared Application
(sqr  Bits/E    f x) = x
(sqr (Bits/O p) f x) = (sqr p @k (f (f k)) x)
(sqr (Bits/I p) f x) = (sqr p @k (f (f k)) (f x))


# Creates an all-zero Bits
_64o =
  (o(o(o(o(o(o(o(o(o(o(o(o(o(o(o(o
  (o(o(o(o(o(o(o(o(o(o(o(o(o(o(o(o
  (o(o(o(o(o(o(o(o(o(o(o(o(o(o(o(o
  (o(o(o(o(o(o(o(o(o(o(o(o(o(o(o(o
  ))))))))))))))))
  ))))))))))))))))
  ))))))))))))))))
  ))))))))))))))))

# 11000000111001
_12345 = (i(o(o(i(i(i(o(o(o(o(o(o(i(i e))))))))))))))

# Bits increment
inc (Bits/O p) = (Bits/I p)
inc (Bits/I p) = (Bits/O (inc p))
inc (Bits/E) = Bits/E

# Addition with carry
add = λa (a
  λap λb (b λbp λap (o (add ap bp)) λbp λap (i       (add ap bp)) e ap)
  λap λb (b λbp λap (i (add ap bp)) λbp λap (o (inc (add ap bp))) e ap)
  λb b)

# Multiplication by squared addition
mul a b = (sqr a (add b) _64o)

main = (mul _12345 _12345)
