/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/FirstSeams
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
/-- Gate 0: first_old_lower_2S1; all 138 nonzero shifted coefficients. -/
private theorem first_old_lower_2S1 (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 0 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 0 x R Z lam =
      11424
      + 11392 * q
      + 19584 * w
      + 19584 * w * q
      + 8192 * w^2
      + 8192 * w^2 * q
      + 89256 * v
      + 89216 * v * q
      + 171136 * v * w
      + 171136 * v * w * q
      + 81920 * v * w^2
      + 81920 * v * w^2 * q
      + 143360 * v^2
      + 143360 * v^2 * q
      + 282624 * v^2 * w
      + 282624 * v^2 * w * q
      + 139264 * v^2 * w^2
      + 139264 * v^2 * w^2 * q
      + 65536 * v^3
      + 65536 * v^3 * q
      + 131072 * v^3 * w
      + 131072 * v^3 * w * q
      + 65536 * v^3 * w^2
      + 65536 * v^3 * w^2 * q
      + 11600 * u
      + 11584 * u * q
      + 19776 * u * w
      + 19776 * u * w * q
      + 8192 * u * w^2
      + 8192 * u * w^2 * q
      + 105810 * u * v
      + 105792 * u * v * q
      + 204096 * u * v * w
      + 204096 * u * v * w * q
      + 98304 * u * v * w^2
      + 98304 * u * v * w^2 * q
      + 176128 * u * v^2
      + 176128 * u * v^2 * q
      + 348160 * u * v^2 * w
      + 348160 * u * v^2 * w * q
      + 172032 * u * v^2 * w^2
      + 172032 * u * v^2 * w^2 * q
      + 81920 * u * v^3
      + 81920 * u * v^3 * q
      + 163840 * u * v^3 * w
      + 163840 * u * v^3 * w * q
      + 81920 * u * v^3 * w^2
      + 81920 * u * v^3 * w^2 * q
      + 4426 * u^2
      + 4424 * u^2 * q
      + 7496 * u^2 * w
      + 7496 * u^2 * w * q
      + 3072 * u^2 * w^2
      + 3072 * u^2 * w^2 * q
      + 49994 * u^2 * v
      + 49992 * u^2 * v * q
      + 97096 * u^2 * v * w
      + 97096 * u^2 * v * w * q
      + 47104 * u^2 * v * w^2
      + 47104 * u^2 * v * w^2 * q
      + 86528 * u^2 * v^2
      + 86528 * u^2 * v^2 * q
      + 171520 * u^2 * v^2 * w
      + 171520 * u^2 * v^2 * w * q
      + 84992 * u^2 * v^2 * w^2
      + 84992 * u^2 * v^2 * w^2 * q
      + 40960 * u^2 * v^3
      + 40960 * u^2 * v^3 * q
      + 81920 * u^2 * v^3 * w
      + 81920 * u^2 * v^3 * w * q
      + 40960 * u^2 * v^3 * w^2
      + 40960 * u^2 * v^3 * w^2 * q
      + 752 * u^3
      + 752 * u^3 * q
      + 1264 * u^3 * w
      + 1264 * u^3 * w * q
      + 512 * u^3 * w^2
      + 512 * u^3 * w^2 * q
      + 11760 * u^3 * v
      + 11760 * u^3 * v * q
      + 23024 * u^3 * v * w
      + 23024 * u^3 * v * w * q
      + 11264 * u^3 * v * w^2
      + 11264 * u^3 * v * w^2 * q
      + 21248 * u^3 * v^2
      + 21248 * u^3 * v^2 * q
      + 42240 * u^3 * v^2 * w
      + 42240 * u^3 * v^2 * w * q
      + 20992 * u^3 * v^2 * w^2
      + 20992 * u^3 * v^2 * w^2 * q
      + 10240 * u^3 * v^3
      + 10240 * u^3 * v^3 * q
      + 20480 * u^3 * v^3 * w
      + 20480 * u^3 * v^3 * w * q
      + 10240 * u^3 * v^3 * w^2
      + 10240 * u^3 * v^3 * w^2 * q
      + 48 * u^4
      + 48 * u^4 * q
      + 80 * u^4 * w
      + 80 * u^4 * w * q
      + 32 * u^4 * w^2
      + 32 * u^4 * w^2 * q
      + 1376 * u^4 * v
      + 1376 * u^4 * v * q
      + 2720 * u^4 * v * w
      + 2720 * u^4 * v * w * q
      + 1344 * u^4 * v * w^2
      + 1344 * u^4 * v * w^2 * q
      + 2608 * u^4 * v^2
      + 2608 * u^4 * v^2 * q
      + 5200 * u^4 * v^2 * w
      + 5200 * u^4 * v^2 * w * q
      + 2592 * u^4 * v^2 * w^2
      + 2592 * u^4 * v^2 * w^2 * q
      + 1280 * u^4 * v^3
      + 1280 * u^4 * v^3 * q
      + 2560 * u^4 * v^3 * w
      + 2560 * u^4 * v^3 * w * q
      + 1280 * u^4 * v^3 * w^2
      + 1280 * u^4 * v^3 * w^2 * q
      + 64 * u^5 * v
      + 64 * u^5 * v * q
      + 128 * u^5 * v * w
      + 128 * u^5 * v * w * q
      + 64 * u^5 * v * w^2
      + 64 * u^5 * v * w^2 * q
      + 128 * u^5 * v^2
      + 128 * u^5 * v^2 * q
      + 256 * u^5 * v^2 * w
      + 256 * u^5 * v^2 * w * q
      + 128 * u^5 * v^2 * w^2
      + 128 * u^5 * v^2 * w^2 * q
      + 64 * u^5 * v^3
      + 64 * u^5 * v^3 * q
      + 128 * u^5 * v^3 * w
      + 128 * u^5 * v^3 * w * q
      + 64 * u^5 * v^3 * w^2
      + 64 * u^5 * v^3 * w^2 * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 1: first_new_lower_2T1; all 144 nonzero shifted coefficients. -/
private theorem first_new_lower_2T1 (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 1 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 1 x R Z lam =
      81096
      + 81024 * q
      + 154752 * w
      + 154752 * w * q
      + 73728 * w^2
      + 73728 * w^2 * q
      + 294096 * v
      + 294016 * v * q
      + 572544 * v * w
      + 572544 * v * w * q
      + 278528 * v * w^2
      + 278528 * v * w^2 * q
      + 344064 * v^2
      + 344064 * v^2 * q
      + 679936 * v^2 * w
      + 679936 * v^2 * w * q
      + 335872 * v^2 * w^2
      + 335872 * v^2 * w^2 * q
      + 131072 * v^3
      + 131072 * v^3 * q
      + 262144 * v^3 * w
      + 262144 * v^3 * w * q
      + 131072 * v^3 * w^2
      + 131072 * v^3 * w^2 * q
      + 97634 * u
      + 97600 * u * q
      + 187712 * u * w
      + 187712 * u * w * q
      + 90112 * u * w^2
      + 90112 * u * w^2 * q
      + 359780 * u * v
      + 359744 * u * v * q
      + 703808 * u * v * w
      + 703808 * u * v * w * q
      + 344064 * u * v * w^2
      + 344064 * u * v * w^2 * q
      + 425984 * u * v^2
      + 425984 * u * v^2 * q
      + 843776 * u * v^2 * w
      + 843776 * u * v^2 * w * q
      + 417792 * u * v^2 * w^2
      + 417792 * u * v^2 * w^2 * q
      + 163840 * u * v^3
      + 163840 * u * v^3 * q
      + 327680 * u * v^3 * w
      + 327680 * u * v^3 * w * q
      + 163840 * u * v^3 * w^2
      + 163840 * u * v^3 * w^2 * q
      + 46924 * u^2
      + 46920 * u^2 * q
      + 90952 * u^2 * w
      + 90952 * u^2 * w * q
      + 44032 * u^2 * w^2
      + 44032 * u^2 * w^2 * q
      + 175948 * u^2 * v
      + 175944 * u^2 * v * q
      + 345928 * u^2 * v * w
      + 345928 * u^2 * v * w * q
      + 169984 * u^2 * v * w^2
      + 169984 * u^2 * v * w^2 * q
      + 210944 * u^2 * v^2
      + 210944 * u^2 * v^2 * q
      + 418816 * u^2 * v^2 * w
      + 418816 * u^2 * v^2 * w * q
      + 207872 * u^2 * v^2 * w^2
      + 207872 * u^2 * v^2 * w^2 * q
      + 81920 * u^2 * v^3
      + 81920 * u^2 * v^3 * q
      + 163840 * u^2 * v^3 * w
      + 163840 * u^2 * v^3 * w * q
      + 81920 * u^2 * v^3 * w^2
      + 81920 * u^2 * v^3 * w^2 * q
      + 11248 * u^3
      + 11248 * u^3 * q
      + 22000 * u^3 * w
      + 22000 * u^3 * w * q
      + 10752 * u^3 * w^2
      + 10752 * u^3 * w^2 * q
      + 42992 * u^3 * v
      + 42992 * u^3 * v * q
      + 84976 * u^3 * v * w
      + 84976 * u^3 * v * w * q
      + 41984 * u^3 * v * w^2
      + 41984 * u^3 * v * w^2 * q
      + 52224 * u^3 * v^2
      + 52224 * u^3 * v^2 * q
      + 103936 * u^3 * v^2 * w
      + 103936 * u^3 * v^2 * w * q
      + 51712 * u^3 * v^2 * w^2
      + 51712 * u^3 * v^2 * w^2 * q
      + 20480 * u^3 * v^3
      + 20480 * u^3 * v^3 * q
      + 40960 * u^3 * v^3 * w
      + 40960 * u^3 * v^3 * w * q
      + 20480 * u^3 * v^3 * w^2
      + 20480 * u^3 * v^3 * w^2 * q
      + 1344 * u^4
      + 1344 * u^4 * q
      + 2656 * u^4 * w
      + 2656 * u^4 * w * q
      + 1312 * u^4 * w^2
      + 1312 * u^4 * w^2 * q
      + 5248 * u^4 * v
      + 5248 * u^4 * v * q
      + 10432 * u^4 * v * w
      + 10432 * u^4 * v * w * q
      + 5184 * u^4 * v * w^2
      + 5184 * u^4 * v * w^2 * q
      + 6464 * u^4 * v^2
      + 6464 * u^4 * v^2 * q
      + 12896 * u^4 * v^2 * w
      + 12896 * u^4 * v^2 * w * q
      + 6432 * u^4 * v^2 * w^2
      + 6432 * u^4 * v^2 * w^2 * q
      + 2560 * u^4 * v^3
      + 2560 * u^4 * v^3 * q
      + 5120 * u^4 * v^3 * w
      + 5120 * u^4 * v^3 * w * q
      + 2560 * u^4 * v^3 * w^2
      + 2560 * u^4 * v^3 * w^2 * q
      + 64 * u^5
      + 64 * u^5 * q
      + 128 * u^5 * w
      + 128 * u^5 * w * q
      + 64 * u^5 * w^2
      + 64 * u^5 * w^2 * q
      + 256 * u^5 * v
      + 256 * u^5 * v * q
      + 512 * u^5 * v * w
      + 512 * u^5 * v * w * q
      + 256 * u^5 * v * w^2
      + 256 * u^5 * v * w^2 * q
      + 320 * u^5 * v^2
      + 320 * u^5 * v^2 * q
      + 640 * u^5 * v^2 * w
      + 640 * u^5 * v^2 * w * q
      + 320 * u^5 * v^2 * w^2
      + 320 * u^5 * v^2 * w^2 * q
      + 128 * u^5 * v^3
      + 128 * u^5 * v^3 * q
      + 256 * u^5 * v^3 * w
      + 256 * u^5 * v^3 * w * q
      + 128 * u^5 * v^3 * w^2
      + 128 * u^5 * v^3 * w^2 * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 2: first_old_upper; all 108 nonzero shifted coefficients. -/
private theorem first_old_upper (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 2 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 2 x R Z lam =
      62432
      + 62464 * q
      + 128000 * w
      + 128000 * w * q
      + 65536 * w^2
      + 65536 * w^2 * q
      + 123864 * v
      + 123904 * v * q
      + 254976 * v * w
      + 254976 * v * w * q
      + 131072 * v * w^2
      + 131072 * v * w^2 * q
      + 61440 * v^2
      + 61440 * v^2 * q
      + 126976 * v^2 * w
      + 126976 * v^2 * w * q
      + 65536 * v^2 * w^2
      + 65536 * v^2 * w^2 * q
      + 78576 * u
      + 78592 * u * q
      + 160512 * u * w
      + 160512 * u * w * q
      + 81920 * u * w^2
      + 81920 * u * w^2 * q
      + 156398 * u * v
      + 156416 * u * v * q
      + 320256 * u * v * w
      + 320256 * u * v * w * q
      + 163840 * u * v * w^2
      + 163840 * u * v * w^2 * q
      + 77824 * u * v^2
      + 77824 * u * v^2 * q
      + 159744 * u * v^2 * w
      + 159744 * u * v^2 * w * q
      + 81920 * u * v^2 * w^2
      + 81920 * u * v^2 * w^2 * q
      + 39614 * u^2
      + 39616 * u^2 * q
      + 80576 * u^2 * w
      + 80576 * u^2 * w * q
      + 40960 * u^2 * w^2
      + 40960 * u^2 * w^2 * q
      + 79038 * u^2 * v
      + 79040 * u^2 * v * q
      + 160960 * u^2 * v * w
      + 160960 * u^2 * v * w * q
      + 81920 * u^2 * v * w^2
      + 81920 * u^2 * v * w^2 * q
      + 39424 * u^2 * v^2
      + 39424 * u^2 * v^2 * q
      + 80384 * u^2 * v^2 * w
      + 80384 * u^2 * v^2 * w * q
      + 40960 * u^2 * v^2 * w^2
      + 40960 * u^2 * v^2 * w^2 * q
      + 10000 * u^3
      + 10000 * u^3 * q
      + 20240 * u^3 * w
      + 20240 * u^3 * w * q
      + 10240 * u^3 * w^2
      + 10240 * u^3 * w^2 * q
      + 19984 * u^3 * v
      + 19984 * u^3 * v * q
      + 40464 * u^3 * v * w
      + 40464 * u^3 * v * w * q
      + 20480 * u^3 * v * w^2
      + 20480 * u^3 * v * w^2 * q
      + 9984 * u^3 * v^2
      + 9984 * u^3 * v^2 * q
      + 20224 * u^3 * v^2 * w
      + 20224 * u^3 * v^2 * w * q
      + 10240 * u^3 * v^2 * w^2
      + 10240 * u^3 * v^2 * w^2 * q
      + 1264 * u^4
      + 1264 * u^4 * q
      + 2544 * u^4 * w
      + 2544 * u^4 * w * q
      + 1280 * u^4 * w^2
      + 1280 * u^4 * w^2 * q
      + 2528 * u^4 * v
      + 2528 * u^4 * v * q
      + 5088 * u^4 * v * w
      + 5088 * u^4 * v * w * q
      + 2560 * u^4 * v * w^2
      + 2560 * u^4 * v * w^2 * q
      + 1264 * u^4 * v^2
      + 1264 * u^4 * v^2 * q
      + 2544 * u^4 * v^2 * w
      + 2544 * u^4 * v^2 * w * q
      + 1280 * u^4 * v^2 * w^2
      + 1280 * u^4 * v^2 * w^2 * q
      + 64 * u^5
      + 64 * u^5 * q
      + 128 * u^5 * w
      + 128 * u^5 * w * q
      + 64 * u^5 * w^2
      + 64 * u^5 * w^2 * q
      + 128 * u^5 * v
      + 128 * u^5 * v * q
      + 256 * u^5 * v * w
      + 256 * u^5 * v * w * q
      + 128 * u^5 * v * w^2
      + 128 * u^5 * v * w^2 * q
      + 64 * u^5 * v^2
      + 64 * u^5 * v^2 * q
      + 128 * u^5 * v^2 * w
      + 128 * u^5 * v^2 * w * q
      + 64 * u^5 * v^2 * w^2
      + 64 * u^5 * v^2 * w^2 * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 3: first_new_upper; all 108 nonzero shifted coefficients. -/
private theorem first_new_upper (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 3 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 3 x R Z lam =
      58296
      + 58368 * q
      + 123904 * w
      + 123904 * w * q
      + 65536 * w^2
      + 65536 * w^2 * q
      + 115632 * v
      + 115712 * v * q
      + 246784 * v * w
      + 246784 * v * w * q
      + 131072 * v * w^2
      + 131072 * v * w^2 * q
      + 57344 * v^2
      + 57344 * v^2 * q
      + 122880 * v^2 * w
      + 122880 * v^2 * w * q
      + 65536 * v^2 * w^2
      + 65536 * v^2 * w^2 * q
      + 74462 * u
      + 74496 * u * q
      + 156416 * u * w
      + 156416 * u * w * q
      + 81920 * u * w^2
      + 81920 * u * w^2 * q
      + 148188 * u * v
      + 148224 * u * v * q
      + 312064 * u * v * w
      + 312064 * u * v * w * q
      + 163840 * u * v * w^2
      + 163840 * u * v * w^2 * q
      + 73728 * u * v^2
      + 73728 * u * v^2 * q
      + 155648 * u * v^2 * w
      + 155648 * u * v^2 * w * q
      + 81920 * u * v^2 * w^2
      + 81920 * u * v^2 * w^2 * q
      + 38076 * u^2
      + 38080 * u^2 * q
      + 79040 * u^2 * w
      + 79040 * u^2 * w * q
      + 40960 * u^2 * w^2
      + 40960 * u^2 * w^2 * q
      + 75964 * u^2 * v
      + 75968 * u^2 * v * q
      + 157888 * u^2 * v * w
      + 157888 * u^2 * v * w * q
      + 81920 * u^2 * v * w^2
      + 81920 * u^2 * v * w^2 * q
      + 37888 * u^2 * v^2
      + 37888 * u^2 * v^2 * q
      + 78848 * u^2 * v^2 * w
      + 78848 * u^2 * v^2 * w * q
      + 40960 * u^2 * v^2 * w^2
      + 40960 * u^2 * v^2 * w^2 * q
      + 9744 * u^3
      + 9744 * u^3 * q
      + 19984 * u^3 * w
      + 19984 * u^3 * w * q
      + 10240 * u^3 * w^2
      + 10240 * u^3 * w^2 * q
      + 19472 * u^3 * v
      + 19472 * u^3 * v * q
      + 39952 * u^3 * v * w
      + 39952 * u^3 * v * w * q
      + 20480 * u^3 * v * w^2
      + 20480 * u^3 * v * w^2 * q
      + 9728 * u^3 * v^2
      + 9728 * u^3 * v^2 * q
      + 19968 * u^3 * v^2 * w
      + 19968 * u^3 * v^2 * w * q
      + 10240 * u^3 * v^2 * w^2
      + 10240 * u^3 * v^2 * w^2 * q
      + 1248 * u^4
      + 1248 * u^4 * q
      + 2528 * u^4 * w
      + 2528 * u^4 * w * q
      + 1280 * u^4 * w^2
      + 1280 * u^4 * w^2 * q
      + 2496 * u^4 * v
      + 2496 * u^4 * v * q
      + 5056 * u^4 * v * w
      + 5056 * u^4 * v * w * q
      + 2560 * u^4 * v * w^2
      + 2560 * u^4 * v * w^2 * q
      + 1248 * u^4 * v^2
      + 1248 * u^4 * v^2 * q
      + 2528 * u^4 * v^2 * w
      + 2528 * u^4 * v^2 * w * q
      + 1280 * u^4 * v^2 * w^2
      + 1280 * u^4 * v^2 * w^2 * q
      + 64 * u^5
      + 64 * u^5 * q
      + 128 * u^5 * w
      + 128 * u^5 * w * q
      + 64 * u^5 * w^2
      + 64 * u^5 * w^2 * q
      + 128 * u^5 * v
      + 128 * u^5 * v * q
      + 256 * u^5 * v * w
      + 256 * u^5 * v * w * q
      + 128 * u^5 * v * w^2
      + 128 * u^5 * v * w^2 * q
      + 64 * u^5 * v^2
      + 64 * u^5 * v^2 * q
      + 128 * u^5 * v^2 * w
      + 128 * u^5 * v^2 * w * q
      + 64 * u^5 * v^2 * w^2
      + 64 * u^5 * v^2 * w^2 * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
