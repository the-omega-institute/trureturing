/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix13
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; premises=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix13.prefix13_checked
   digest: Exact prime progression coverage and deletion prefix inequalities. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.PrefixChecker

/-! Finite progression witnesses and exact natural-number comparisons. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Arith.MakowskiSchinzel.Certificate.Data

/-- Certified exclusion table for the progression with modulus `6`. -/
def prefix52 : PrefixCertificate where
  r := 3
  forbidden :=
    [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
     101, 103, 107, 109, 113, 127, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
     197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  table :=
    [7, 13, 19, 37, 73, 97, 109, 163, 193, 433, 487, 577, 769, 787, 1153, 1297, 1459, 1579,
     1627, 1663, 1699, 1759, 1867, 1879, 1987, 2083, 2203, 2239, 2383, 2593, 2659, 2767, 2803,
     2917, 3019, 3229, 3253, 3343, 3373, 3457, 3463, 3517]
  factors :=
    [0, 0, 0, 0, 5, 0, 0, 0, 7, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 5,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 13, 0, 0, 0, 0, 0, 5,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 11, 5, 0, 0, 0, 0, 5,
     0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 23, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5,
     0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 43, 5, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 17, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 43, 0, 0,
     5, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All progression and product checks for this block. -/
theorem prefix13_checked :
    ([prefix52].all (·.check)) = true := by
  decide

end D5.S3.Arith.MakowskiSchinzel.Certificate.Data
