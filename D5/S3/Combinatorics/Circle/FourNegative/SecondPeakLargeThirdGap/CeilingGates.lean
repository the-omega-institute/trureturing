/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/CeilingGates
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
/-- Gate 4: ceil_E_lower; all 168 nonzero shifted coefficients. -/
private theorem ceil_E_lower (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 4 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 4 x R Z lam =
      217434
      + 217472 * q
      + 438656 * w
      + 438656 * w * q
      + 221184 * w^2
      + 221184 * w^2 * q
      + 631128 * v
      + 631168 * v * q
      + 1270144 * v * w
      + 1270144 * v * w * q
      + 638976 * v * w^2
      + 638976 * v * w^2 * q
      + 610304 * v^2
      + 610304 * v^2 * q
      + 1224704 * v^2 * w
      + 1224704 * v^2 * w * q
      + 614400 * v^2 * w^2
      + 614400 * v^2 * w^2 * q
      + 196608 * v^3
      + 196608 * v^3 * q
      + 393216 * v^3 * w
      + 393216 * v^3 * w * q
      + 196608 * v^3 * w^2
      + 196608 * v^3 * w^2 * q
      + 340271 * u
      + 340288 * u * q
      + 684352 * u * w
      + 684352 * u * w * q
      + 344064 * u * w^2
      + 344064 * u * w^2 * q
      + 991534 * u * v
      + 991552 * u * v * q
      + 1990976 * u * v * w
      + 1990976 * u * v * w * q
      + 999424 * u * v * w^2
      + 999424 * u * v * w^2 * q
      + 962560 * u * v^2
      + 962560 * u * v^2 * q
      + 1929216 * u * v^2 * w
      + 1929216 * u * v^2 * w * q
      + 966656 * u * v^2 * w^2
      + 966656 * u * v^2 * w^2 * q
      + 311296 * u * v^3
      + 311296 * u * v^3 * q
      + 622592 * u * v^3 * w
      + 622592 * u * v^3 * w * q
      + 311296 * u * v^3 * w^2
      + 311296 * u * v^3 * w^2 * q
      + 220758 * u^2
      + 220760 * u^2 * q
      + 442968 * u^2 * w
      + 442968 * u^2 * w * q
      + 222208 * u^2 * w^2
      + 222208 * u^2 * w^2 * q
      + 646230 * u^2 * v
      + 646232 * u^2 * v * q
      + 1295448 * u^2 * v * w
      + 1295448 * u^2 * v * w * q
      + 649216 * u^2 * v * w^2
      + 649216 * u^2 * v * w^2 * q
      + 630272 * u^2 * v^2
      + 630272 * u^2 * v^2 * q
      + 1262080 * u^2 * v^2 * w
      + 1262080 * u^2 * v^2 * w * q
      + 631808 * u^2 * v^2 * w^2
      + 631808 * u^2 * v^2 * w^2 * q
      + 204800 * u^2 * v^3
      + 204800 * u^2 * v^3 * q
      + 409600 * u^2 * v^3 * w
      + 409600 * u^2 * v^3 * w * q
      + 204800 * u^2 * v^3 * w^2
      + 204800 * u^2 * v^3 * w^2 * q
      + 76040 * u^3
      + 76040 * u^3 * q
      + 152328 * u^3 * w
      + 152328 * u^3 * w * q
      + 76288 * u^3 * w^2
      + 76288 * u^3 * w^2 * q
      + 223752 * u^3 * v
      + 223752 * u^3 * v * q
      + 448008 * u^3 * v * w
      + 448008 * u^3 * v * w * q
      + 224256 * u^3 * v * w^2
      + 224256 * u^3 * v * w^2 * q
      + 219392 * u^3 * v^2
      + 219392 * u^3 * v^2 * q
      + 439040 * u^3 * v^2 * w
      + 439040 * u^3 * v^2 * w * q
      + 219648 * u^3 * v^2 * w^2
      + 219648 * u^3 * v^2 * w^2 * q
      + 71680 * u^3 * v^3
      + 71680 * u^3 * v^3 * q
      + 143360 * u^3 * v^3 * w
      + 143360 * u^3 * v^3 * w * q
      + 71680 * u^3 * v^3 * w^2
      + 71680 * u^3 * v^3 * w^2 * q
      + 14672 * u^4
      + 14672 * u^4 * q
      + 29360 * u^4 * w
      + 29360 * u^4 * w * q
      + 14688 * u^4 * w^2
      + 14688 * u^4 * w^2 * q
      + 43424 * u^4 * v
      + 43424 * u^4 * v * q
      + 86880 * u^4 * v * w
      + 86880 * u^4 * v * w * q
      + 43456 * u^4 * v * w^2
      + 43456 * u^4 * v * w^2 * q
      + 42832 * u^4 * v^2
      + 42832 * u^4 * v^2 * q
      + 85680 * u^4 * v^2 * w
      + 85680 * u^4 * v^2 * w * q
      + 42848 * u^4 * v^2 * w^2
      + 42848 * u^4 * v^2 * w^2 * q
      + 14080 * u^4 * v^3
      + 14080 * u^4 * v^3 * q
      + 28160 * u^4 * v^3 * w
      + 28160 * u^4 * v^3 * w * q
      + 14080 * u^4 * v^3 * w^2
      + 14080 * u^4 * v^3 * w^2 * q
      + 1504 * u^5
      + 1504 * u^5 * q
      + 3008 * u^5 * w
      + 3008 * u^5 * w * q
      + 1504 * u^5 * w^2
      + 1504 * u^5 * w^2 * q
      + 4480 * u^5 * v
      + 4480 * u^5 * v * q
      + 8960 * u^5 * v * w
      + 8960 * u^5 * v * w * q
      + 4480 * u^5 * v * w^2
      + 4480 * u^5 * v * w^2 * q
      + 4448 * u^5 * v^2
      + 4448 * u^5 * v^2 * q
      + 8896 * u^5 * v^2 * w
      + 8896 * u^5 * v^2 * w * q
      + 4448 * u^5 * v^2 * w^2
      + 4448 * u^5 * v^2 * w^2 * q
      + 1472 * u^5 * v^3
      + 1472 * u^5 * v^3 * q
      + 2944 * u^5 * v^3 * w
      + 2944 * u^5 * v^3 * w * q
      + 1472 * u^5 * v^3 * w^2
      + 1472 * u^5 * v^3 * w^2 * q
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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Normalize the full explicit shifted polynomial and all its nonnegative monomials.
/-- Gate 5: ceil_H_upper; all 144 nonzero shifted coefficients. -/
private theorem ceil_H_upper (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 5 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 5 x R Z lam =
      113316
      + 113278 * q
      + 227968 * w
      + 227968 * w * q
      + 114688 * w^2
      + 114688 * w^2 * q
      + 358056 * v
      + 358016 * v * q
      + 718464 * v * w
      + 718464 * v * w * q
      + 360448 * v * w^2
      + 360448 * v * w^2 * q
      + 375808 * v^2
      + 375808 * v^2 * q
      + 752640 * v^2 * w
      + 752640 * v^2 * w * q
      + 376832 * v^2 * w^2
      + 376832 * v^2 * w^2 * q
      + 131072 * v^3
      + 131072 * v^3 * q
      + 262144 * v^3 * w
      + 262144 * v^3 * w * q
      + 131072 * v^3 * w^2
      + 131072 * v^3 * w^2 * q
      + 138193 * u
      + 138176 * u * q
      + 277440 * u * w
      + 277440 * u * w * q
      + 139264 * u * w^2
      + 139264 * u * w^2 * q
      + 440530 * u * v
      + 440512 * u * v * q
      + 882880 * u * v * w
      + 882880 * u * v * w * q
      + 442368 * u * v * w^2
      + 442368 * u * v * w^2 * q
      + 466176 * u * v^2
      + 466176 * u * v^2 * q
      + 933120 * u * v^2 * w
      + 933120 * u * v^2 * w * q
      + 466944 * u * v^2 * w^2
      + 466944 * u * v^2 * w^2 * q
      + 163840 * u * v^3
      + 163840 * u * v^3 * q
      + 327680 * u * v^3 * w
      + 327680 * u * v^3 * w * q
      + 163840 * u * v^3 * w^2
      + 163840 * u * v^3 * w^2 * q
      + 67306 * u^2
      + 67304 * u^2 * q
      + 134888 * u^2 * w
      + 134888 * u^2 * w * q
      + 67584 * u^2 * w^2
      + 67584 * u^2 * w^2 * q
      + 216618 * u^2 * v
      + 216616 * u^2 * v * q
      + 433704 * u^2 * v * w
      + 433704 * u^2 * v * w * q
      + 217088 * u^2 * v * w^2
      + 217088 * u^2 * v * w^2 * q
      + 231232 * u^2 * v^2
      + 231232 * u^2 * v^2 * q
      + 462656 * u^2 * v^2 * w
      + 462656 * u^2 * v^2 * w * q
      + 231424 * u^2 * v^2 * w^2
      + 231424 * u^2 * v^2 * w^2 * q
      + 81920 * u^2 * v^3
      + 81920 * u^2 * v^3 * q
      + 163840 * u^2 * v^3 * w
      + 163840 * u^2 * v^3 * w * q
      + 81920 * u^2 * v^3 * w^2
      + 81920 * u^2 * v^3 * w^2 * q
      + 16360 * u^3
      + 16360 * u^3 * q
      + 32744 * u^3 * w
      + 32744 * u^3 * w * q
      + 16384 * u^3 * w^2
      + 16384 * u^3 * w^2 * q
      + 53208 * u^3 * v
      + 53208 * u^3 * v * q
      + 106456 * u^3 * v * w
      + 106456 * u^3 * v * w * q
      + 53248 * u^3 * v * w^2
      + 53248 * u^3 * v * w^2 * q
      + 57328 * u^3 * v^2
      + 57328 * u^3 * v^2 * q
      + 114672 * u^3 * v^2 * w
      + 114672 * u^3 * v^2 * w * q
      + 57344 * u^3 * v^2 * w^2
      + 57344 * u^3 * v^2 * w^2 * q
      + 20480 * u^3 * v^3
      + 20480 * u^3 * v^3 * q
      + 40960 * u^3 * v^3 * w
      + 40960 * u^3 * v^3 * w * q
      + 20480 * u^3 * v^3 * w^2
      + 20480 * u^3 * v^3 * w^2 * q
      + 1984 * u^4
      + 1984 * u^4 * q
      + 3968 * u^4 * w
      + 3968 * u^4 * w * q
      + 1984 * u^4 * w^2
      + 1984 * u^4 * w^2 * q
      + 6528 * u^4 * v
      + 6528 * u^4 * v * q
      + 13056 * u^4 * v * w
      + 13056 * u^4 * v * w * q
      + 6528 * u^4 * v * w^2
      + 6528 * u^4 * v * w^2 * q
      + 7104 * u^4 * v^2
      + 7104 * u^4 * v^2 * q
      + 14208 * u^4 * v^2 * w
      + 14208 * u^4 * v^2 * w * q
      + 7104 * u^4 * v^2 * w^2
      + 7104 * u^4 * v^2 * w^2 * q
      + 2560 * u^4 * v^3
      + 2560 * u^4 * v^3 * q
      + 5120 * u^4 * v^3 * w
      + 5120 * u^4 * v^3 * w * q
      + 2560 * u^4 * v^3 * w^2
      + 2560 * u^4 * v^3 * w^2 * q
      + 96 * u^5
      + 96 * u^5 * q
      + 192 * u^5 * w
      + 192 * u^5 * w * q
      + 96 * u^5 * w^2
      + 96 * u^5 * w^2 * q
      + 320 * u^5 * v
      + 320 * u^5 * v * q
      + 640 * u^5 * v * w
      + 640 * u^5 * v * w * q
      + 320 * u^5 * v * w^2
      + 320 * u^5 * v * w^2 * q
      + 352 * u^5 * v^2
      + 352 * u^5 * v^2 * q
      + 704 * u^5 * v^2 * w
      + 704 * u^5 * v^2 * w * q
      + 352 * u^5 * v^2 * w^2
      + 352 * u^5 * v^2 * w^2 * q
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
/-- Gate 6: ceil_old_cap; all 108 nonzero shifted coefficients. -/
private theorem ceil_old_cap (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    0 ≤ gate 6 x R Z lam := by
  let u := x-4
  let v := R-1
  let w := Z-1
  let q := lam-1
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hw : 0 ≤ w := by dsimp [w]; omega
  have hq : 0 ≤ q := by dsimp [q]; omega
  have expansion : gate 6 x R Z lam =
      28034
      + 28030 * q
      + 60800 * w
      + 60800 * w * q
      + 32768 * w^2
      + 32768 * w^2 * q
      + 55680 * v
      + 55680 * v * q
      + 121216 * v * w
      + 121216 * v * w * q
      + 65536 * v * w^2
      + 65536 * v * w^2 * q
      + 27648 * v^2
      + 27648 * v^2 * q
      + 60416 * v^2 * w
      + 60416 * v^2 * w * q
      + 32768 * v^2 * w^2
      + 32768 * v^2 * w^2 * q
      + 36417 * u
      + 36416 * u * q
      + 77376 * u * w
      + 77376 * u * w * q
      + 40960 * u * w^2
      + 40960 * u * w^2 * q
      + 72512 * u * v
      + 72512 * u * v * q
      + 154432 * u * v * w
      + 154432 * u * v * w * q
      + 81920 * u * v * w^2
      + 81920 * u * v * w^2 * q
      + 36096 * u * v^2
      + 36096 * u * v^2 * q
      + 77056 * u * v^2 * w
      + 77056 * u * v^2 * w * q
      + 40960 * u * v^2 * w^2
      + 40960 * u * v^2 * w^2 * q
      + 18840 * u^2
      + 18840 * u^2 * q
      + 39320 * u^2 * w
      + 39320 * u^2 * w * q
      + 20480 * u^2 * w^2
      + 20480 * u^2 * w^2 * q
      + 37592 * u^2 * v
      + 37592 * u^2 * v * q
      + 78552 * u^2 * v * w
      + 78552 * u^2 * v * w * q
      + 40960 * u^2 * v * w^2
      + 40960 * u^2 * v * w^2 * q
      + 18752 * u^2 * v^2
      + 18752 * u^2 * v^2 * q
      + 39232 * u^2 * v^2 * w
      + 39232 * u^2 * v^2 * w * q
      + 20480 * u^2 * v^2 * w^2
      + 20480 * u^2 * v^2 * w^2 * q
      + 4856 * u^3
      + 4856 * u^3 * q
      + 9976 * u^3 * w
      + 9976 * u^3 * w * q
      + 5120 * u^3 * w^2
      + 5120 * u^3 * w^2 * q
      + 9704 * u^3 * v
      + 9704 * u^3 * v * q
      + 19944 * u^3 * v * w
      + 19944 * u^3 * v * w * q
      + 10240 * u^3 * v * w^2
      + 10240 * u^3 * v * w^2 * q
      + 4848 * u^3 * v^2
      + 4848 * u^3 * v^2 * q
      + 9968 * u^3 * v^2 * w
      + 9968 * u^3 * v^2 * w * q
      + 5120 * u^3 * v^2 * w^2
      + 5120 * u^3 * v^2 * w^2 * q
      + 624 * u^4
      + 624 * u^4 * q
      + 1264 * u^4 * w
      + 1264 * u^4 * w * q
      + 640 * u^4 * w^2
      + 640 * u^4 * w^2 * q
      + 1248 * u^4 * v
      + 1248 * u^4 * v * q
      + 2528 * u^4 * v * w
      + 2528 * u^4 * v * w * q
      + 1280 * u^4 * v * w^2
      + 1280 * u^4 * v * w^2 * q
      + 624 * u^4 * v^2
      + 624 * u^4 * v^2 * q
      + 1264 * u^4 * v^2 * w
      + 1264 * u^4 * v^2 * w * q
      + 640 * u^4 * v^2 * w^2
      + 640 * u^4 * v^2 * w^2 * q
      + 32 * u^5
      + 32 * u^5 * q
      + 64 * u^5 * w
      + 64 * u^5 * w * q
      + 32 * u^5 * w^2
      + 32 * u^5 * w^2 * q
      + 64 * u^5 * v
      + 64 * u^5 * v * q
      + 128 * u^5 * v * w
      + 128 * u^5 * v * w * q
      + 64 * u^5 * v * w^2
      + 64 * u^5 * v * w^2 * q
      + 32 * u^5 * v^2
      + 32 * u^5 * v^2 * q
      + 64 * u^5 * v^2 * w
      + 64 * u^5 * v^2 * w * q
      + 32 * u^5 * v^2 * w^2
      + 32 * u^5 * v^2 * w^2 * q := by
    dsimp [gate, dyadicT, dyadicZ, dyadicY, DD, AA, BB, LL, MM, NN, BBn, LLn, MMn, EE, KK, JJ, u, v, w, q]
    ring
  rw [expansion]
  positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
