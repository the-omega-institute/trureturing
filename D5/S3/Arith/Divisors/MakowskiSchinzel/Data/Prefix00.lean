/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix00
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; premises=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix00.prefix00_checked
   digest: Exact prime progression coverage and deletion prefix inequalities. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.PrefixChecker

/-! Finite progression witnesses and exact natural-number comparisons. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Arith.MakowskiSchinzel.Certificate.Data

/-- Certified exclusion table for the progression with modulus `14`. -/
def prefix00 : PrefixCertificate where
  r := 7
  forbidden :=
    []
  table :=
    [29, 43, 71, 113, 127, 197, 211, 239, 281, 337, 379, 421, 449, 463, 491, 547, 617, 631, 659,
     673, 701, 743, 757, 827, 883, 911, 953, 967, 1009, 1051, 1093, 1163, 1289, 1303, 1373,
     1429, 1471, 1499, 1583, 1597, 1667, 1709]
  factors :=
    [0, 3, 0, 0, 3, 0, 5, 3, 0, 0, 3, 5, 13, 3, 0, 0, 3, 0, 11, 3, 0, 5, 3, 17, 0, 3, 5, 0, 3,
     11, 0, 3, 0, 0, 3, 0, 5, 3, 13, 0, 3, 5, 19, 3, 0, 0, 3, 0, 0, 3, 0, 5, 3, 0, 0, 3, 5, 17,
     3, 0, 29, 3, 11, 0, 3, 0, 5, 3, 0, 0, 3, 5, 0, 3, 17, 0, 3, 13, 0, 3, 19, 5, 3, 0, 11, 3,
     5, 23, 3, 29, 13, 3, 0, 0, 3, 11, 5, 3, 0, 19, 3, 5, 0, 3, 31, 0, 3, 0, 17, 3, 23, 5, 3, 0,
     0, 3, 5, 11, 3, 0, 41, 3, 0]

/-- Certified exclusion table for the progression with modulus `26`. -/
def prefix01 : PrefixCertificate where
  r := 13
  forbidden :=
    []
  table :=
    [53, 79, 131, 157, 313, 443, 521, 547, 599, 677, 859, 911, 937, 1093, 1171, 1223, 1249,
     1301, 1327, 1483, 1613, 1847, 1873, 1951, 2003, 2029, 2081, 2237, 2341, 2393, 2549, 2731,
     2861, 2887, 2939, 3121, 3251, 3329, 3407, 3433, 3511, 3719]
  factors :=
    [0, 3, 0, 0, 3, 0, 0, 3, 11, 5, 3, 7, 0, 3, 5, 17, 3, 0, 7, 3, 0, 0, 3, 0, 5, 3, 0, 19, 3,
     5, 11, 3, 7, 0, 3, 0, 0, 3, 23, 5, 3, 11, 0, 3, 5, 0, 3, 0, 0, 3, 0, 0, 3, 7, 5, 3, 31, 0,
     3, 5, 7, 3, 0, 11, 3, 19, 17, 3, 29, 5, 3, 0, 0, 3, 5, 0, 3, 0, 0, 3, 0, 7, 3, 17, 5, 3, 0,
     31, 3, 5, 0, 3, 0, 41, 3, 7, 11, 3, 0, 5, 3, 37, 7, 3, 5, 0, 3, 11, 53, 3, 0, 0, 3, 0, 5,
     3, 7, 17, 3, 5, 0, 3, 19, 7, 3, 0, 29, 3, 0, 5, 3, 0, 0, 3, 5, 0, 3, 7, 37, 3, 11, 19, 3, 0]

/-- Certified exclusion table for the progression with modulus `34`. -/
def prefix02 : PrefixCertificate where
  r := 17
  forbidden :=
    []
  table :=
    [103, 137, 239, 307, 409, 443, 613, 647, 919, 953, 1021, 1123, 1259, 1327, 1361, 1429, 1531,
     1667, 1871, 1973, 2143, 2347, 2381, 2551, 2687, 2789, 2857, 3061, 3163, 3299, 3469, 3571,
     3673, 3877, 3911, 4013, 4217, 4421, 4523, 4591, 4931, 4999]
  factors :=
    [0, 5, 3, 0, 0, 3, 5, 0, 3, 0, 11, 3, 0, 0, 3, 7, 5, 3, 0, 0, 3, 5, 7, 3, 19, 23, 3, 0, 0,
     3, 0, 5, 3, 0, 13, 3, 5, 0, 3, 0, 0, 3, 0, 7, 3, 0, 5, 3, 23, 0, 3, 5, 29, 3, 11, 0, 3, 7,
     0, 3, 13, 5, 3, 0, 7, 3, 5, 43, 3, 0, 0, 3, 31, 13, 3, 0, 5, 3, 7, 0, 3, 5, 0, 3, 0, 7, 3,
     11, 41, 3, 0, 5, 3, 0, 23, 3, 5, 0, 3, 7, 19, 3, 0, 31, 3, 0, 5, 3, 0, 11, 3, 5, 13, 3, 0,
     0, 3, 23, 0, 3, 7, 5, 3, 47, 0, 3, 5, 7, 3, 41, 0, 3, 67, 0, 3, 0, 5, 3, 13, 29, 3, 5, 11,
     3, 59, 0, 3, 0]

/-- Certified exclusion table for the progression with modulus `38`. -/
def prefix03 : PrefixCertificate where
  r := 19
  forbidden :=
    []
  table :=
    [191, 229, 419, 457, 571, 647, 761, 1103, 1217, 1483, 1559, 1597, 1787, 1901, 2053, 2129,
     2243, 2281, 2357, 2699, 2851, 2927, 3041, 3079, 3307, 3877, 4219, 4409, 4447, 4523, 4561,
     4637, 4751, 4789, 4903, 5701, 6043, 6271, 6689, 6803, 6841, 6917]
  factors :=
    [0, 3, 7, 5, 3, 0, 0, 3, 5, 7, 3, 0, 0, 3, 13, 0, 3, 0, 5, 3, 0, 17, 3, 5, 11, 3, 23, 13, 3,
     0, 7, 3, 0, 5, 3, 11, 37, 3, 5, 0, 3, 0, 0, 3, 7, 29, 3, 0, 5, 3, 0, 7, 3, 5, 0, 3, 0, 11,
     3, 0, 0, 3, 0, 5, 3, 7, 13, 3, 5, 43, 3, 0, 7, 3, 29, 0, 3, 0, 5, 3, 0, 0, 3, 5, 31, 3, 7,
     0, 3, 17, 11, 3, 13, 5, 3, 23, 41, 3, 5, 53, 3, 11, 0, 3, 59, 13, 3, 7, 5, 3, 37, 0, 3, 5,
     7, 3, 0, 0, 3, 0, 0, 3, 0, 5, 3, 0, 0, 3, 5, 0, 3, 13, 29, 3, 11, 7, 3, 41, 5, 3, 17, 23,
     3, 5, 13, 3, 31, 37, 3, 7, 0, 3, 53, 5, 3, 43, 7, 3, 5, 0, 3, 29, 47, 3, 23, 0, 3, 11, 5,
     3, 7, 67, 3, 5, 17, 3, 0, 7, 3, 0, 0, 3, 0]

/-- All progression and product checks for this block. -/
theorem prefix00_checked :
    ([prefix00, prefix01, prefix02, prefix03].all (·.check)) = true := by
  decide

end D5.S3.Arith.MakowskiSchinzel.Certificate.Data
