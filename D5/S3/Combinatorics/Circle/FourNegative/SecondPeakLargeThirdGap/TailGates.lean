/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/TailGates
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Complete shifted polynomial identities; each coefficient is explicit. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Algebra

/-! Complete shifted polynomial identities; each coefficient is explicit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
open private gate dyadicT dyadicZ dyadicY DD AA BB LL MM NN BBn LLn MMn EE KK JJ from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Algebra

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 9: third_old_lower_S3; all 60 nonzero shifted coefficients. -/
private theorem third_old_lower_S3 (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 9 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 9 x R Z lam =
      1512
      + 1471 * q
      + 1472 * w
      + 1472 * w * q
      + 3048 * v
      + 3008 * v * q
      + 3008 * v * w
      + 3008 * v * w * q
      + 1536 * v^2
      + 1536 * v^2 * q
      + 1536 * v^2 * w
      + 1536 * v^2 * w * q
      + 1650 * u
      + 1632 * u * q
      + 1632 * u * w
      + 1632 * u * w * q
      + 3314 * u * v
      + 3296 * u * v * q
      + 3296 * u * v * w
      + 3296 * u * v * w * q
      + 1664 * u * v^2
      + 1664 * u * v^2 * q
      + 1664 * u * v^2 * w
      + 1664 * u * v^2 * w * q
      + 670 * u^2
      + 668 * u^2 * q
      + 668 * u^2 * w
      + 668 * u^2 * w * q
      + 1342 * u^2 * v
      + 1340 * u^2 * v * q
      + 1340 * u^2 * v * w
      + 1340 * u^2 * v * w * q
      + 672 * u^2 * v^2
      + 672 * u^2 * v^2 * q
      + 672 * u^2 * v^2 * w
      + 672 * u^2 * v^2 * w * q
      + 120 * u^3
      + 120 * u^3 * q
      + 120 * u^3 * w
      + 120 * u^3 * w * q
      + 240 * u^3 * v
      + 240 * u^3 * v * q
      + 240 * u^3 * v * w
      + 240 * u^3 * v * w * q
      + 120 * u^3 * v^2
      + 120 * u^3 * v^2 * q
      + 120 * u^3 * v^2 * w
      + 120 * u^3 * v^2 * w * q
      + 8 * u^4
      + 8 * u^4 * q
      + 8 * u^4 * w
      + 8 * u^4 * w * q
      + 16 * u^4 * v
      + 16 * u^4 * v * q
      + 16 * u^4 * v * w
      + 16 * u^4 * v * w * q
      + 8 * u^4 * v^2
      + 8 * u^4 * v^2 * q
      + 8 * u^4 * v^2 * w
      + 8 * u^4 * v^2 * w * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 10: third_new_lower_T3; all 60 nonzero shifted coefficients. -/
private theorem third_new_lower_T3 (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 10 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 10 x R Z lam =
      3088
      + 3007 * q
      + 3008 * w
      + 3008 * w * q
      + 6160 * v
      + 6080 * v * q
      + 6080 * v * w
      + 6080 * v * w * q
      + 3072 * v^2
      + 3072 * v^2 * q
      + 3072 * v^2 * w
      + 3072 * v^2 * w * q
      + 3332 * u
      + 3296 * u * q
      + 3296 * u * w
      + 3296 * u * w * q
      + 6660 * u * v
      + 6624 * u * v * q
      + 6624 * u * v * w
      + 6624 * u * v * w * q
      + 3328 * u * v^2
      + 3328 * u * v^2 * q
      + 3328 * u * v^2 * w
      + 3328 * u * v^2 * w * q
      + 1344 * u^2
      + 1340 * u^2 * q
      + 1340 * u^2 * w
      + 1340 * u^2 * w * q
      + 2688 * u^2 * v
      + 2684 * u^2 * v * q
      + 2684 * u^2 * v * w
      + 2684 * u^2 * v * w * q
      + 1344 * u^2 * v^2
      + 1344 * u^2 * v^2 * q
      + 1344 * u^2 * v^2 * w
      + 1344 * u^2 * v^2 * w * q
      + 240 * u^3
      + 240 * u^3 * q
      + 240 * u^3 * w
      + 240 * u^3 * w * q
      + 480 * u^3 * v
      + 480 * u^3 * v * q
      + 480 * u^3 * v * w
      + 480 * u^3 * v * w * q
      + 240 * u^3 * v^2
      + 240 * u^3 * v^2 * q
      + 240 * u^3 * v^2 * w
      + 240 * u^3 * v^2 * w * q
      + 16 * u^4
      + 16 * u^4 * q
      + 16 * u^4 * w
      + 16 * u^4 * w * q
      + 32 * u^4 * v
      + 32 * u^4 * v * q
      + 32 * u^4 * v * w
      + 32 * u^4 * v * w * q
      + 16 * u^4 * v^2
      + 16 * u^4 * v^2 * q
      + 16 * u^4 * v^2 * w
      + 16 * u^4 * v^2 * w * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 11: third_old_upper; all 48 nonzero shifted coefficients. -/
private theorem third_old_upper (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 11 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 11 x R Z lam =
      1112
      + 1154 * q
      + 1152 * w
      + 1152 * w * q
      + 2136 * v
      + 2176 * v * q
      + 2176 * v * w
      + 2176 * v * w * q
      + 1024 * v^2
      + 1024 * v^2 * q
      + 1024 * v^2 * w
      + 1024 * v^2 * w * q
      + 814 * u
      + 832 * u * q
      + 832 * u * w
      + 832 * u * w * q
      + 1582 * u * v
      + 1600 * u * v * q
      + 1600 * u * v * w
      + 1600 * u * v * w * q
      + 768 * u * v^2
      + 768 * u * v^2 * q
      + 768 * u * v^2 * w
      + 768 * u * v^2 * w * q
      + 198 * u^2
      + 200 * u^2 * q
      + 200 * u^2 * w
      + 200 * u^2 * w * q
      + 390 * u^2 * v
      + 392 * u^2 * v * q
      + 392 * u^2 * v * w
      + 392 * u^2 * v * w * q
      + 192 * u^2 * v^2
      + 192 * u^2 * v^2 * q
      + 192 * u^2 * v^2 * w
      + 192 * u^2 * v^2 * w * q
      + 16 * u^3
      + 16 * u^3 * q
      + 16 * u^3 * w
      + 16 * u^3 * w * q
      + 32 * u^3 * v
      + 32 * u^3 * v * q
      + 32 * u^3 * v * w
      + 32 * u^3 * v * w * q
      + 16 * u^3 * v^2
      + 16 * u^3 * v^2 * q
      + 16 * u^3 * v^2 * w
      + 16 * u^3 * v^2 * w * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 12: third_new_upper; all 48 nonzero shifted coefficients. -/
private theorem third_new_upper (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 12 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 12 x R Z lam =
      2096
      + 2178 * q
      + 2176 * w
      + 2176 * w * q
      + 4144 * v
      + 4224 * v * q
      + 4224 * v * w
      + 4224 * v * w * q
      + 2048 * v^2
      + 2048 * v^2 * q
      + 2048 * v^2 * w
      + 2048 * v^2 * w * q
      + 1564 * u
      + 1600 * u * q
      + 1600 * u * w
      + 1600 * u * w * q
      + 3100 * u * v
      + 3136 * u * v * q
      + 3136 * u * v * w
      + 3136 * u * v * w * q
      + 1536 * u * v^2
      + 1536 * u * v^2 * q
      + 1536 * u * v^2 * w
      + 1536 * u * v^2 * w * q
      + 388 * u^2
      + 392 * u^2 * q
      + 392 * u^2 * w
      + 392 * u^2 * w * q
      + 772 * u^2 * v
      + 776 * u^2 * v * q
      + 776 * u^2 * v * w
      + 776 * u^2 * v * w * q
      + 384 * u^2 * v^2
      + 384 * u^2 * v^2 * q
      + 384 * u^2 * v^2 * w
      + 384 * u^2 * v^2 * w * q
      + 32 * u^3
      + 32 * u^3 * q
      + 32 * u^3 * w
      + 32 * u^3 * w * q
      + 64 * u^3 * v
      + 64 * u^3 * v * q
      + 64 * u^3 * v * w
      + 64 * u^3 * v * w * q
      + 32 * u^3 * v^2
      + 32 * u^3 * v^2 * q
      + 32 * u^3 * v^2 * w
      + 32 * u^3 * v^2 * w * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 13: fresh_N_minus_A; all 168 nonzero shifted coefficients. -/
private theorem fresh_N_minus_A (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 13 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 13 x R Z lam =
      228858
      + 228864 * q
      + 458240 * w
      + 458240 * w * q
      + 229376 * w^2
      + 229376 * w^2 * q
      + 720384 * v
      + 720384 * v * q
      + 1441280 * v * w
      + 1441280 * v * w * q
      + 720896 * v * w^2
      + 720896 * v * w^2 * q
      + 753664 * v^2
      + 753664 * v^2 * q
      + 1507328 * v^2 * w
      + 1507328 * v^2 * w * q
      + 753664 * v^2 * w^2
      + 753664 * v^2 * w^2 * q
      + 262144 * v^3
      + 262144 * v^3 * q
      + 524288 * v^3 * w
      + 524288 * v^3 * w * q
      + 262144 * v^3 * w^2
      + 262144 * v^3 * w^2 * q
      + 351871 * u
      + 351872 * u * q
      + 704128 * u * w
      + 704128 * u * w * q
      + 352256 * u * w^2
      + 352256 * u * w^2 * q
      + 1097344 * u * v
      + 1097344 * u * v * q
      + 2195072 * u * v * w
      + 2195072 * u * v * w * q
      + 1097728 * u * v * w^2
      + 1097728 * u * v * w^2 * q
      + 1138688 * u * v^2
      + 1138688 * u * v^2 * q
      + 2277376 * u * v^2 * w
      + 2277376 * u * v^2 * w * q
      + 1138688 * u * v^2 * w^2
      + 1138688 * u * v^2 * w^2 * q
      + 393216 * u * v^3
      + 393216 * u * v^3 * q
      + 786432 * u * v^3 * w
      + 786432 * u * v^3 * w * q
      + 393216 * u * v^3 * w^2
      + 393216 * u * v^3 * w^2 * q
      + 225184 * u^2
      + 225184 * u^2 * q
      + 450464 * u^2 * w
      + 450464 * u^2 * w * q
      + 225280 * u^2 * w^2
      + 225280 * u^2 * w^2 * q
      + 696224 * u^2 * v
      + 696224 * u^2 * v * q
      + 1392544 * u^2 * v * w
      + 1392544 * u^2 * v * w * q
      + 696320 * u^2 * v * w^2
      + 696320 * u^2 * v * w^2 * q
      + 716800 * u^2 * v^2
      + 716800 * u^2 * v^2 * q
      + 1433600 * u^2 * v^2 * w
      + 1433600 * u^2 * v^2 * w * q
      + 716800 * u^2 * v^2 * w^2
      + 716800 * u^2 * v^2 * w^2 * q
      + 245760 * u^2 * v^3
      + 245760 * u^2 * v^3 * q
      + 491520 * u^2 * v^3 * w
      + 491520 * u^2 * v^3 * w * q
      + 245760 * u^2 * v^3 * w^2
      + 245760 * u^2 * v^3 * w^2 * q
      + 76792 * u^3
      + 76792 * u^3 * q
      + 153592 * u^3 * w
      + 153592 * u^3 * w * q
      + 76800 * u^3 * w^2
      + 76800 * u^3 * w^2 * q
      + 235512 * u^3 * v
      + 235512 * u^3 * v * q
      + 471032 * u^3 * v * w
      + 471032 * u^3 * v * w * q
      + 235520 * u^3 * v * w^2
      + 235520 * u^3 * v * w^2 * q
      + 240640 * u^3 * v^2
      + 240640 * u^3 * v^2 * q
      + 481280 * u^3 * v^2 * w
      + 481280 * u^3 * v^2 * w * q
      + 240640 * u^3 * v^2 * w^2
      + 240640 * u^3 * v^2 * w^2 * q
      + 81920 * u^3 * v^3
      + 81920 * u^3 * v^3 * q
      + 163840 * u^3 * v^3 * w
      + 163840 * u^3 * v^3 * w * q
      + 81920 * u^3 * v^3 * w^2
      + 81920 * u^3 * v^3 * w^2 * q
      + 14720 * u^4
      + 14720 * u^4 * q
      + 29440 * u^4 * w
      + 29440 * u^4 * w * q
      + 14720 * u^4 * w^2
      + 14720 * u^4 * w^2 * q
      + 44800 * u^4 * v
      + 44800 * u^4 * v * q
      + 89600 * u^4 * v * w
      + 89600 * u^4 * v * w * q
      + 44800 * u^4 * v * w^2
      + 44800 * u^4 * v * w^2 * q
      + 45440 * u^4 * v^2
      + 45440 * u^4 * v^2 * q
      + 90880 * u^4 * v^2 * w
      + 90880 * u^4 * v^2 * w * q
      + 45440 * u^4 * v^2 * w^2
      + 45440 * u^4 * v^2 * w^2 * q
      + 15360 * u^4 * v^3
      + 15360 * u^4 * v^3 * q
      + 30720 * u^4 * v^3 * w
      + 30720 * u^4 * v^3 * w * q
      + 15360 * u^4 * v^3 * w^2
      + 15360 * u^4 * v^3 * w^2 * q
      + 1504 * u^5
      + 1504 * u^5 * q
      + 3008 * u^5 * w
      + 3008 * u^5 * w * q
      + 1504 * u^5 * w^2
      + 1504 * u^5 * w^2 * q
      + 4544 * u^5 * v
      + 4544 * u^5 * v * q
      + 9088 * u^5 * v * w
      + 9088 * u^5 * v * w * q
      + 4544 * u^5 * v * w^2
      + 4544 * u^5 * v * w^2 * q
      + 4576 * u^5 * v^2
      + 4576 * u^5 * v^2 * q
      + 9152 * u^5 * v^2 * w
      + 9152 * u^5 * v^2 * w * q
      + 4576 * u^5 * v^2 * w^2
      + 4576 * u^5 * v^2 * w^2 * q
      + 1536 * u^5 * v^3
      + 1536 * u^5 * v^3 * q
      + 3072 * u^5 * v^3 * w
      + 3072 * u^5 * v^3 * w * q
      + 1536 * u^5 * v^3 * w^2
      + 1536 * u^5 * v^3 * w^2 * q
      + 64 * u^6
      + 64 * u^6 * q
      + 128 * u^6 * w
      + 128 * u^6 * w * q
      + 64 * u^6 * w^2
      + 64 * u^6 * w^2 * q
      + 192 * u^6 * v
      + 192 * u^6 * v * q
      + 384 * u^6 * v * w
      + 384 * u^6 * v * w * q
      + 192 * u^6 * v * w^2
      + 192 * u^6 * v * w^2 * q
      + 192 * u^6 * v^2
      + 192 * u^6 * v^2 * q
      + 384 * u^6 * v^2 * w
      + 384 * u^6 * v^2 * w * q
      + 192 * u^6 * v^2 * w^2
      + 192 * u^6 * v^2 * w^2 * q
      + 64 * u^6 * v^3
      + 64 * u^6 * v^3 * q
      + 128 * u^6 * v^3 * w
      + 128 * u^6 * v^3 * w * q
      + 64 * u^6 * v^3 * w^2
      + 64 * u^6 * v^3 * w^2 * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
