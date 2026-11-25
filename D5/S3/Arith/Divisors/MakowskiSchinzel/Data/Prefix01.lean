/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix01
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; premises=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix01.prefix01_checked
   digest: Exact prime progression coverage and deletion prefix inequalities. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.PrefixChecker

/-! Finite progression witnesses and exact natural-number comparisons. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Arith.MakowskiSchinzel.Certificate.Data

/-- Certified exclusion table for the progression with modulus `62`. -/
def prefix04 : PrefixCertificate where
  r := 31
  forbidden :=
    []
  table :=
    [311, 373, 683, 1117, 1303, 1427, 1489, 1613, 1861, 2357, 2543, 2729, 2791, 3163, 3659,
     3907, 4093, 4217, 4651, 5023, 5147, 5209, 5333, 5519, 5581, 5953, 6263, 6449, 6883, 7069,
     7193, 7937, 8123, 8681, 8867, 8929, 9239, 9859, 10169, 10789, 11161, 11471]
  factors :=
    [0, 3, 5, 11, 3, 0, 0, 3, 7, 13, 3, 0, 5, 3, 11, 7, 3, 5, 0, 3, 17, 0, 3, 0, 0, 3, 0, 5, 3,
     7, 0, 3, 5, 23, 3, 13, 7, 3, 0, 41, 3, 0, 5, 3, 0, 0, 3, 5, 13, 3, 7, 0, 3, 19, 17, 3, 23,
     5, 3, 0, 61, 3, 5, 0, 3, 29, 0, 3, 0, 11, 3, 7, 5, 3, 13, 0, 3, 5, 7, 3, 11, 0, 3, 0, 0, 3,
     0, 5, 3, 0, 0, 3, 5, 73, 3, 43, 0, 3, 59, 7, 3, 0, 5, 3, 0, 17, 3, 5, 37, 3, 19, 0, 3, 7,
     0, 3, 0, 5, 3, 47, 7, 3, 5, 29, 3, 23, 13, 3, 0, 19, 3, 0, 5, 3, 7, 11, 3, 5, 43, 3, 0, 7,
     3, 0, 0, 3, 11, 5, 3, 0, 71, 3, 5, 53, 3, 7, 17, 3, 97, 0, 3, 67, 5, 3, 0, 13, 3, 5, 11, 3,
     83, 23, 3, 17, 0, 3, 7, 5, 3, 11, 0, 3, 5, 7, 3, 0]

/-- Certified exclusion table for the progression with modulus `74`. -/
def prefix05 : PrefixCertificate where
  r := 37
  forbidden :=
    []
  table :=
    [149, 223, 593, 1259, 1481, 1777, 1999, 2221, 2591, 2887, 3109, 3257, 3331, 3701, 3923,
     4219, 4441, 4663, 5107, 5477, 6143, 6217, 6661, 6883, 7253, 7549, 7919, 7993, 8363, 8807,
     9029, 9103, 9473, 9547, 9769, 10139, 10657, 11027, 11471, 12211, 12433, 13099]
  factors :=
    [0, 3, 0, 0, 3, 7, 5, 3, 0, 23, 3, 5, 7, 3, 17, 11, 3, 0, 31, 3, 0, 5, 3, 13, 0, 3, 5, 0, 3,
     19, 0, 3, 23, 7, 3, 0, 5, 3, 29, 0, 3, 5, 0, 3, 0, 0, 3, 7, 11, 3, 0, 5, 3, 0, 7, 3, 5, 0,
     3, 11, 0, 3, 13, 0, 3, 17, 5, 3, 7, 0, 3, 5, 73, 3, 0, 7, 3, 41, 23, 3, 31, 5, 3, 0, 0, 3,
     5, 47, 3, 7, 0, 3, 11, 0, 3, 79, 5, 3, 0, 17, 3, 5, 0, 3, 43, 19, 3, 0, 0, 3, 7, 5, 3, 0,
     11, 3, 5, 7, 3, 0, 83, 3, 0, 0, 3, 11, 5, 3, 0, 0, 3, 5, 0, 3, 47, 97, 3, 0, 7, 3, 13, 5,
     3, 19, 0, 3, 5, 11, 3, 0, 17, 3, 7, 13, 3, 0, 5, 3, 11, 7, 3, 5, 19, 3, 53, 0, 3, 17, 0, 3,
     23, 5, 3, 7, 79, 3, 5, 0]

/-- Certified exclusion table for the progression with modulus `82`. -/
def prefix06 : PrefixCertificate where
  r := 41
  forbidden :=
    []
  table :=
    [83, 739, 821, 1231, 1559, 1723, 2297, 2543, 2707, 2789, 2953, 3527, 3691, 4019, 5003, 5167,
     5413, 5659, 5741, 5987, 6151, 6397, 6971, 7873, 8447, 8693, 9103, 9349, 9431, 9677, 9923,
     10169, 10333, 11071, 11317, 11399, 12301, 12547, 13121, 13367, 13613, 13859]
  factors :=
    [0, 0, 3, 13, 7, 3, 17, 5, 3, 0, 0, 3, 5, 11, 3, 0, 13, 3, 7, 0, 3, 0, 5, 3, 11, 7, 3, 5, 0,
     3, 23, 0, 3, 0, 0, 3, 0, 5, 3, 7, 17, 3, 5, 0, 3, 0, 7, 3, 31, 0, 3, 47, 5, 3, 43, 13, 3,
     5, 67, 3, 7, 0, 3, 0, 29, 3, 0, 5, 3, 0, 0, 3, 5, 0, 3, 0, 23, 3, 0, 11, 3, 7, 5, 3, 83, 0,
     3, 5, 7, 3, 11, 17, 3, 29, 13, 3, 0, 5, 3, 23, 59, 3, 5, 0, 3, 79, 0, 3, 17, 7, 3, 0, 5, 3,
     0, 0, 3, 5, 0, 3, 13, 0, 3, 7, 0, 3, 0, 5, 3, 71, 7, 3, 5, 13, 3, 0, 19, 3, 0, 0, 3, 31, 5,
     3, 7, 11, 3, 5, 53, 3, 0, 7, 3, 0, 73, 3, 11, 5, 3, 13, 0, 3, 5, 0, 3, 7, 0, 3, 23, 0]

/-- Certified exclusion table for the progression with modulus `86`. -/
def prefix07 : PrefixCertificate where
  r := 43
  forbidden :=
    []
  table :=
    [173, 431, 947, 1033, 1291, 1549, 1721, 1979, 2237, 2753, 3011, 3527, 3613, 4129, 4817,
     4903, 5333, 5419, 5591, 5849, 6451, 6709, 6967, 7741, 8171, 8429, 9203, 9461, 9547, 9719,
     10321, 10837, 11353, 11783, 12041, 13159, 13331, 13417, 13933, 14449, 14621, 14879]
  factors :=
    [0, 3, 0, 7, 3, 0, 11, 3, 13, 5, 3, 0, 0, 3, 5, 0, 3, 7, 0, 3, 0, 13, 3, 0, 5, 3, 0, 23, 3,
     5, 29, 3, 0, 17, 3, 0, 19, 3, 7, 5, 3, 0, 0, 3, 5, 7, 3, 13, 0, 3, 11, 41, 3, 47, 5, 3, 0,
     0, 3, 5, 13, 3, 0, 0, 3, 0, 7, 3, 0, 5, 3, 31, 11, 3, 5, 0, 3, 37, 0, 3, 7, 0, 3, 11, 5, 3,
     13, 7, 3, 5, 0, 3, 41, 19, 3, 0, 23, 3, 0, 5, 3, 7, 31, 3, 5, 11, 3, 0, 7, 3, 0, 0, 3, 0,
     5, 3, 11, 29, 3, 5, 0, 3, 7, 71, 3, 13, 0, 3, 101, 5, 3, 19, 0, 3, 5, 17, 3, 0, 11, 3, 0,
     67, 3, 7, 5, 3, 29, 47, 3, 5, 7, 3, 17, 0, 3, 0, 0, 3, 107, 5, 3, 61, 0, 3, 5, 23, 3, 53,
     0, 3, 0, 7, 3, 0]

/-- All progression and product checks for this block. -/
theorem prefix01_checked :
    ([prefix04, prefix05, prefix06, prefix07].all (·.check)) = true := by
  decide

end D5.S3.Arith.MakowskiSchinzel.Certificate.Data
