/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Joint
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; premises=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Joint.both_checked,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Joint.joint_checked
   digest: Exact shared-class ranks and the joint support-count certificate. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.PrefixChecker
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix12

/-! Joint prime tables and all support-count thresholds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Arith.MakowskiSchinzel.Certificate.Data

/-- A complete lower-rank table for the shared class. -/
def bothCertificate : PrefixCertificate where
  r := 55
  forbidden :=
    [7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
     103, 107, 109, 113, 127, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
     199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  table :=
    [331, 661, 881, 991, 1321, 2971, 3301, 3631, 4951, 5281, 5501, 9901, 10891, 12101, 13751,
     14081, 14411, 14851, 19801, 21121, 23761, 26731, 30911, 34211, 34871, 35201, 42131, 44111,
     46091, 47521, 48731, 49391, 52691, 54011, 55001, 55331, 57641, 59621, 62591, 63361, 71171,
     74471]
  factors :=
    [0, 3, 13, 0, 3, 19, 0, 0, 0, 0, 3, 7, 0, 0, 0, 13, 3, 0, 7, 0, 31, 0, 3, 0, 19, 3, 0, 0, 0,
     0, 0, 0, 7, 0, 0, 0, 17, 0, 0, 0, 3, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 3, 0, 0,
     0, 0, 7, 0, 0, 0, 3, 0, 53, 0, 0, 0, 0, 0, 89, 0, 0, 37, 0, 0, 0, 0, 13, 7, 0, 0, 0, 0, 0,
     0, 3, 0, 0, 0, 0, 0, 0, 0, 59, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 109, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 43, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0,
     0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 71, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 7, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 17, 0, 7, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 7, 113,
     0, 0, 0, 0, 127, 7, 3, 0, 0, 0, 13, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 13, 0, 0, 0, 0,
     167, 0, 0, 0, 37, 0, 0, 61, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 29, 0, 0, 0, 0, 0, 31, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 3, 0, 0,
     3, 13, 0, 0, 0, 0, 0, 17, 199, 0, 0, 73, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 7, 0, 0, 0, 3, 0,
     0, 0, 0, 53, 0, 0, 0, 0, 7, 0, 0, 0, 17, 0, 0, 7, 3, 0, 0, 3, 0, 0, 0, 0, 13, 0, 0, 0, 3,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 3, 0, 0, 0, 0, 0, 3,
     29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 17, 0, 3, 0, 0, 0, 47, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 193, 3, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0,
     0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 223, 0, 3, 0, 0, 3,
     0, 241, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 191, 3, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 149,
     0, 0, 7, 0, 0, 0, 0, 3, 17, 0, 0, 23, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
     0, 3, 13, 0, 0, 0, 0, 0, 37, 19, 0, 0, 0, 0, 7, 13, 3, 0, 0, 0, 61, 0, 3, 0, 0, 0, 0, 0, 3,
     17, 0, 0, 67, 0, 3, 0, 0, 3, 0, 0, 3, 13, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 3, 7, 0,
     3, 0, 0, 0, 0, 7, 0, 0, 0, 0, 109, 0, 3, 0, 0, 0, 71, 79, 3, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 3, 151, 41, 0, 0]

/-- Threshold pairs for the only-five and only-eleven classes. -/
def jointThresholds : List (ℕ × ℕ) :=
    [(43, 43), (33, 42), (27, 41), (24, 40), (21, 35), (20, 25), (19, 21), (19, 19), (18, 17),
     (18, 16), (18, 15), (17, 15), (17, 15), (17, 14), (17, 14), (17, 14), (17, 14), (17, 14),
     (17, 13), (17, 13), (17, 13), (17, 13), (17, 13), (17, 13), (16, 13), (16, 13), (16, 13),
     (16, 13), (15, 13), (14, 13), (13, 12), (12, 12), (11, 11), (10, 10), (9, 9), (8, 8),
     (7, 7), (6, 6), (5, 5), (4, 4), (3, 3), (2, 2), (1, 1)]

/-- All lower-rank and geometric comparisons for the shared table hold exactly. -/
theorem both_checked : bothCertificate.check = true := by decide

/-- All joint count triples of total at most forty-two are excluded. -/
theorem joint_checked :
    checkJoint 42 prefix50.table prefix51.table bothCertificate.table jointThresholds = true := by
  decide

#print axioms both_checked
#print axioms joint_checked

end D5.S3.Arith.MakowskiSchinzel.Certificate.Data
