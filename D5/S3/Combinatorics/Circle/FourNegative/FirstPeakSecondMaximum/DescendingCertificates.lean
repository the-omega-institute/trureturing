/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/DescendingCertificates
   generality: I
   mirror-B: none(waiver:private-consumed-construction)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Descending certificates for the physical first-peak joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingArithmetic

/-! DescendingCertificates for the paired physical source construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
open private D A B L M E delta eps width oldSeam newSeam oldNext newNext
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingArithmetic

-- interior/B-2L: 32 terms; constant 391.
set_option maxHeartbeats 1600000 in
private theorem cert_interior_separation (n y z t : ℤ) (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : 2 * y ≤ t) :
    0 < B n y t-2 * L n z t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ t-2 * y := by omega
  have hid : B n y t-2 * L n z t =
      391 + 57 * (t-2 * y) + 2 * (t-2 * y) ^ 2 + 194 * (z-4) + 14 * (z-4) * (t-2 * y) +
      24 * (z-4) ^ 2 + 626 * (y-2 * z) + 72 * (y-2 * z) * (t-2 * y) +
      2 * (y-2 * z) * (t-2 * y) ^ 2 + 284 * (y-2 * z) * (z-4) +
      16 * (y-2 * z) * (z-4) * (t-2 * y) + 32 * (y-2 * z) * (z-4) ^ 2 + 136 * (y-2 * z) ^ 2 +
      8 * (y-2 * z) ^ 2 * (t-2 * y) + 32 * (y-2 * z) ^ 2 * (z-4) + 8 * (y-2 * z) ^ 3 +
      256 * (n-2) + 32 * (n-2) * (t-2 * y) + 1 * (n-2) * (t-2 * y) ^ 2 + 128 * (n-2) * (z-4) +
      8 * (n-2) * (z-4) * (t-2 * y) + 16 * (n-2) * (z-4) ^ 2 + 320 * (n-2) * (y-2 * z) +
      36 * (n-2) * (y-2 * z) * (t-2 * y) + 1 * (n-2) * (y-2 * z) * (t-2 * y) ^ 2 +
      144 * (n-2) * (y-2 * z) * (z-4) + 8 * (n-2) * (y-2 * z) * (z-4) * (t-2 * y) +
      16 * (n-2) * (y-2 * z) * (z-4) ^ 2 + 68 * (n-2) * (y-2 * z) ^ 2 +
      4 * (n-2) * (y-2 * z) ^ 2 * (t-2 * y) + 16 * (n-2) * (y-2 * z) ^ 2 * (z-4) +
      4 * (n-2) * (y-2 * z) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- interior/L-RM: 32 terms; constant 1011.
set_option maxHeartbeats 1600000 in
private theorem cert_interior_remainder (n y z t : ℤ) (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : 2 * y ≤ t) :
    0 < L n z t-n * M y z t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ t-2 * y := by omega
  have hid : L n z t-n * M y z t =
      1011 + 196 * (t-2 * y) + 8 * (t-2 * y) ^ 2 + 765 * (z-4) + 97 * (z-4) * (t-2 * y) +
      2 * (z-4) * (t-2 * y) ^ 2 + 192 * (z-4) ^ 2 + 12 * (z-4) ^ 2 * (t-2 * y) +
      16 * (z-4) ^ 3 + 254 * (y-2 * z) + 24 * (y-2 * z) * (t-2 * y) + 128 * (y-2 * z) * (z-4) +
      6 * (y-2 * z) * (z-4) * (t-2 * y) + 16 * (y-2 * z) * (z-4) ^ 2 + 16 * (y-2 * z) ^ 2 +
      4 * (y-2 * z) ^ 2 * (z-4) + 471 * (n-2) + 96 * (n-2) * (t-2 * y) +
      4 * (n-2) * (t-2 * y) ^ 2 + 366 * (n-2) * (z-4) + 48 * (n-2) * (z-4) * (t-2 * y) +
      1 * (n-2) * (z-4) * (t-2 * y) ^ 2 + 94 * (n-2) * (z-4) ^ 2 +
      6 * (n-2) * (z-4) ^ 2 * (t-2 * y) + 8 * (n-2) * (z-4) ^ 3 + 123 * (n-2) * (y-2 * z) +
      12 * (n-2) * (y-2 * z) * (t-2 * y) + 63 * (n-2) * (y-2 * z) * (z-4) +
      3 * (n-2) * (y-2 * z) * (z-4) * (t-2 * y) + 8 * (n-2) * (y-2 * z) * (z-4) ^ 2 +
      8 * (n-2) * (y-2 * z) ^ 2 + 2 * (n-2) * (y-2 * z) ^ 2 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- interior/width: 32 terms; constant 515.
set_option maxHeartbeats 1600000 in
private theorem cert_interior_width (n y z t : ℤ) (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : 2 * y ≤ t) :
    0 < L n z t-E n y z-2 * width n y z t n := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ t-2 * y := by omega
  have hid : L n z t-E n y z-2 * width n y z t n =
      515 + 160 * (t-2 * y) + 8 * (t-2 * y) ^ 2 + 529 * (z-4) + 89 * (z-4) * (t-2 * y) +
      2 * (z-4) * (t-2 * y) ^ 2 + 164 * (z-4) ^ 2 + 12 * (z-4) ^ 2 * (t-2 * y) +
      16 * (z-4) ^ 3 + 128 * (y-2 * z) + 20 * (y-2 * z) * (t-2 * y) + 98 * (y-2 * z) * (z-4) +
      6 * (y-2 * z) * (z-4) * (t-2 * y) + 16 * (y-2 * z) * (z-4) ^ 2 + 8 * (y-2 * z) ^ 2 +
      4 * (y-2 * z) ^ 2 * (z-4) + 777 * (n-2) + 110 * (n-2) * (t-2 * y) +
      4 * (n-2) * (t-2 * y) ^ 2 + 650 * (n-2) * (z-4) + 60 * (n-2) * (z-4) * (t-2 * y) +
      1 * (n-2) * (z-4) * (t-2 * y) ^ 2 + 178 * (n-2) * (z-4) ^ 2 +
      8 * (n-2) * (z-4) ^ 2 * (t-2 * y) + 16 * (n-2) * (z-4) ^ 3 + 193 * (n-2) * (y-2 * z) +
      14 * (n-2) * (y-2 * z) * (t-2 * y) + 113 * (n-2) * (y-2 * z) * (z-4) +
      4 * (n-2) * (y-2 * z) * (z-4) * (t-2 * y) + 16 * (n-2) * (y-2 * z) * (z-4) ^ 2 +
      12 * (n-2) * (y-2 * z) ^ 2 + 4 * (n-2) * (y-2 * z) ^ 2 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- interior/v-cap: 56 terms; constant 11758.
set_option maxHeartbeats 1600000 in
private theorem cert_interior_capacity (n y z t : ℤ) (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : 2 * y ≤ t) :
    0 < t * A n y z t-2 * B n y t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ t-2 * y := by omega
  have hid : t * A n y z t-2 * B n y t =
      11758 + 1471 * (t-2 * y) + 46 * (t-2 * y) ^ 2 + 13052 * (z-4) + 1264 * (z-4) * (t-2 * y) +
      28 * (z-4) * (t-2 * y) ^ 2 + 5344 * (z-4) ^ 2 + 352 * (z-4) ^ 2 * (t-2 * y) +
      4 * (z-4) ^ 2 * (t-2 * y) ^ 2 + 960 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (t-2 * y) +
      64 * (z-4) ^ 4 + 4478 * (y-2 * z) + 376 * (y-2 * z) * (t-2 * y) +
      6 * (y-2 * z) * (t-2 * y) ^ 2 + 3808 * (y-2 * z) * (z-4) +
      224 * (y-2 * z) * (z-4) * (t-2 * y) + 2 * (y-2 * z) * (z-4) * (t-2 * y) ^ 2 +
      1056 * (y-2 * z) * (z-4) ^ 2 + 32 * (y-2 * z) * (z-4) ^ 2 * (t-2 * y) +
      96 * (y-2 * z) * (z-4) ^ 3 + 568 * (y-2 * z) ^ 2 + 24 * (y-2 * z) ^ 2 * (t-2 * y) +
      336 * (y-2 * z) ^ 2 * (z-4) + 8 * (y-2 * z) ^ 2 * (z-4) * (t-2 * y) +
      48 * (y-2 * z) ^ 2 * (z-4) ^ 2 + 24 * (y-2 * z) ^ 3 + 8 * (y-2 * z) ^ 3 * (z-4) +
      5888 * (n-2) + 736 * (n-2) * (t-2 * y) + 23 * (n-2) * (t-2 * y) ^ 2 +
      6528 * (n-2) * (z-4) + 632 * (n-2) * (z-4) * (t-2 * y) +
      14 * (n-2) * (z-4) * (t-2 * y) ^ 2 + 2672 * (n-2) * (z-4) ^ 2 +
      176 * (n-2) * (z-4) ^ 2 * (t-2 * y) + 2 * (n-2) * (z-4) ^ 2 * (t-2 * y) ^ 2 +
      480 * (n-2) * (z-4) ^ 3 + 16 * (n-2) * (z-4) ^ 3 * (t-2 * y) + 32 * (n-2) * (z-4) ^ 4 +
      2240 * (n-2) * (y-2 * z) + 188 * (n-2) * (y-2 * z) * (t-2 * y) +
      3 * (n-2) * (y-2 * z) * (t-2 * y) ^ 2 + 1904 * (n-2) * (y-2 * z) * (z-4) +
      112 * (n-2) * (y-2 * z) * (z-4) * (t-2 * y) + 
      1 * (n-2) * (y-2 * z) * (z-4) * (t-2 * y) ^ 2 + 528 * (n-2) * (y-2 * z) * (z-4) ^ 2 +
      16 * (n-2) * (y-2 * z) * (z-4) ^ 2 * (t-2 * y) + 48 * (n-2) * (y-2 * z) * (z-4) ^ 3 +
      284 * (n-2) * (y-2 * z) ^ 2 + 12 * (n-2) * (y-2 * z) ^ 2 * (t-2 * y) +
      168 * (n-2) * (y-2 * z) ^ 2 * (z-4) + 4 * (n-2) * (y-2 * z) ^ 2 * (z-4) * (t-2 * y) +
      24 * (n-2) * (y-2 * z) ^ 2 * (z-4) ^ 2 + 12 * (n-2) * (y-2 * z) ^ 3 +
      4 * (n-2) * (y-2 * z) ^ 3 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_eight/B-2L: 9 terms; constant 447.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_eight_separation (y z : ℤ) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < B 8 y y-2 * L 8 z y := by
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : B 8 y y-2 * L 8 z y =
      447 + 224 * (z-4) + 28 * (z-4) ^ 2 + 633 * (y-2 * z) + 286 * (y-2 * z) * (z-4) +
      32 * (y-2 * z) * (z-4) ^ 2 + 136 * (y-2 * z) ^ 2 + 32 * (y-2 * z) ^ 2 * (z-4) +
      8 * (y-2 * z) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_eight/L-RM: 9 terms; constant 6.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_eight_remainder (y z : ℤ) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < L 8 z y-7 * M y z y := by
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : L 8 z y-7 * M y z y =
      6 + 83 * (z-4) + 36 * (z-4) ^ 2 + 4 * (z-4) ^ 3 + 33 * (y-2 * z) +
      26 * (y-2 * z) * (z-4) + 4 * (y-2 * z) * (z-4) ^ 2 + 4 * (y-2 * z) ^ 2 +
      1 * (y-2 * z) ^ 2 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_eight/width: 8 terms; constant 71.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_eight_width (y z : ℤ) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < L 8 z y-E 8 y z-2 * width 8 y z y 7 := by
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : L 8 z y-E 8 y z-2 * width 8 y z y 7 =
      71 + 313 * (z-4) + 138 * (z-4) ^ 2 + 16 * (z-4) ^ 3 + 8 * (y-2 * z) +
      69 * (y-2 * z) * (z-4) + 16 * (y-2 * z) * (z-4) ^ 2 + 4 * (y-2 * z) ^ 2 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_eight/v-cap: 14 terms; constant 11766.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_eight_capacity (y z : ℤ) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < y * A 8 y z y-2 * B 8 y y := by
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : y * A 8 y z y-2 * B 8 y y =
      11766 + 13054 * (z-4) + 5344 * (z-4) ^ 2 + 960 * (z-4) ^ 3 + 64 * (z-4) ^ 4 +
      4479 * (y-2 * z) + 3808 * (y-2 * z) * (z-4) + 1056 * (y-2 * z) * (z-4) ^ 2 +
      96 * (y-2 * z) * (z-4) ^ 3 + 568 * (y-2 * z) ^ 2 + 336 * (y-2 * z) ^ 2 * (z-4) +
      48 * (y-2 * z) ^ 2 * (z-4) ^ 2 + 24 * (y-2 * z) ^ 3 + 8 * (y-2 * z) ^ 3 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_large/B-2L: 18 terms; constant 959.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_large_separation (n y z : ℤ) (hn : 16 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < B n y y-2 * L n z y := by
  have hN : 0 ≤ n-16 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : B n y y-2 * L n z y =
      959 + 480 * (z-4) + 60 * (z-4) ^ 2 + 1273 * (y-2 * z) + 574 * (y-2 * z) * (z-4) +
      64 * (y-2 * z) * (z-4) ^ 2 + 272 * (y-2 * z) ^ 2 + 64 * (y-2 * z) ^ 2 * (z-4) +
      16 * (y-2 * z) ^ 3 + 64 * (n-16) + 32 * (n-16) * (z-4) + 4 * (n-16) * (z-4) ^ 2 +
      80 * (n-16) * (y-2 * z) + 36 * (n-16) * (y-2 * z) * (z-4) +
      4 * (n-16) * (y-2 * z) * (z-4) ^ 2 + 17 * (n-16) * (y-2 * z) ^ 2 +
      4 * (n-16) * (y-2 * z) ^ 2 * (z-4) + 1 * (n-16) * (y-2 * z) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_large/L-M: 18 terms; constant 3836.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_large_lower (n y z : ℤ) (hn : 16 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < L n z y-M y z y := by
  have hN : 0 ≤ n-16 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : L n z y-M y z y =
      3836 + 2879 * (z-4) + 720 * (z-4) ^ 2 + 60 * (z-4) ^ 3 + 959 * (y-2 * z) +
      480 * (y-2 * z) * (z-4) + 60 * (y-2 * z) * (z-4) ^ 2 + 60 * (y-2 * z) ^ 2 +
      15 * (y-2 * z) ^ 2 * (z-4) + 256 * (n-16) + 192 * (n-16) * (z-4) +
      48 * (n-16) * (z-4) ^ 2 + 4 * (n-16) * (z-4) ^ 3 + 64 * (n-16) * (y-2 * z) +
      32 * (n-16) * (y-2 * z) * (z-4) + 4 * (n-16) * (y-2 * z) * (z-4) ^ 2 +
      4 * (n-16) * (y-2 * z) ^ 2 + 1 * (n-16) * (y-2 * z) ^ 2 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_large/nM-L: 10 terms; constant 619.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_large_upper (n y z : ℤ) (hn : 16 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < n * M y z y-L n z y := by
  have hN : 0 ≤ n-16 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : n * M y z y-L n z y =
      619 + 271 * (z-4) + 30 * (z-4) ^ 2 + 76 * (y-2 * z) + 15 * (y-2 * z) * (z-4) +
      41 * (n-16) + 18 * (n-16) * (z-4) + 2 * (n-16) * (z-4) ^ 2 + 5 * (n-16) * (y-2 * z) +
      1 * (n-16) * (y-2 * z) * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_large/width: 18 terms; constant 57.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_large_width (n y z : ℤ) (hn : 16 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < 3 * L n z y-E n y z-2 * A n y z y-4 * M y z y := by
  have hN : 0 ≤ n-16 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : 3 * L n z y-E n y z-2 * A n y z y-4 * M y z y =
      57 + 907 * (z-4) + 414 * (z-4) ^ 2 + 48 * (z-4) ^ 3 + 136 * (y-2 * z) +
      239 * (y-2 * z) * (z-4) + 48 * (y-2 * z) * (z-4) ^ 2 + 16 * (y-2 * z) ^ 2 +
      12 * (y-2 * z) ^ 2 * (z-4) + 71 * (n-16) + 106 * (n-16) * (z-4) +
      38 * (n-16) * (z-4) ^ 2 + 4 * (n-16) * (z-4) ^ 3 + 25 * (n-16) * (y-2 * z) +
      23 * (n-16) * (y-2 * z) * (z-4) + 4 * (n-16) * (y-2 * z) * (z-4) ^ 2 +
      2 * (n-16) * (y-2 * z) ^ 2 + 1 * (n-16) * (y-2 * z) ^ 2 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- boundary_large/v-cap: 28 terms; constant 23542.
set_option maxHeartbeats 1600000 in
private theorem cert_boundary_large_capacity (n y z : ℤ) (hn : 16 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) :
    0 < y * A n y z y-2 * B n y y := by
  have hN : 0 ≤ n-16 := by omega
  have hY : 0 ≤ y-2 * z := by omega
  have hZ : 0 ≤ z-4 := by omega
  have hid : y * A n y z y-2 * B n y y =
      23542 + 26110 * (z-4) + 10688 * (z-4) ^ 2 + 1920 * (z-4) ^ 3 + 128 * (z-4) ^ 4 +
      8959 * (y-2 * z) + 7616 * (y-2 * z) * (z-4) + 2112 * (y-2 * z) * (z-4) ^ 2 +
      192 * (y-2 * z) * (z-4) ^ 3 + 1136 * (y-2 * z) ^ 2 + 672 * (y-2 * z) ^ 2 * (z-4) +
      96 * (y-2 * z) ^ 2 * (z-4) ^ 2 + 48 * (y-2 * z) ^ 3 + 16 * (y-2 * z) ^ 3 * (z-4) +
      1472 * (n-16) + 1632 * (n-16) * (z-4) + 668 * (n-16) * (z-4) ^ 2 +
      120 * (n-16) * (z-4) ^ 3 + 8 * (n-16) * (z-4) ^ 4 + 560 * (n-16) * (y-2 * z) +
      476 * (n-16) * (y-2 * z) * (z-4) + 132 * (n-16) * (y-2 * z) * (z-4) ^ 2 +
      12 * (n-16) * (y-2 * z) * (z-4) ^ 3 + 71 * (n-16) * (y-2 * z) ^ 2 +
      42 * (n-16) * (y-2 * z) ^ 2 * (z-4) + 6 * (n-16) * (y-2 * z) ^ 2 * (z-4) ^ 2 +
      3 * (n-16) * (y-2 * z) ^ 3 + 1 * (n-16) * (y-2 * z) ^ 3 * (z-4) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_seam_0: 9 terms; constant 126.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_seam_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) =
      126 + 384 * (u-1) + 256 * (u-1) ^ 2 + 64 * (z-4) + 192 * (z-4) * (u-1) +
      128 * (z-4) * (u-1) ^ 2 + 8 * (z-4) ^ 2 + 24 * (z-4) ^ 2 * (u-1) +
      16 * (z-4) ^ 2 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_peak_slack_0: 12 terms; constant 530.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_peak_slack_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 2 (2 * z * u) z (2 * z * u) 0-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 2 (2 * z * u) z (2 * z * u) 0-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) =
      530 + 912 * (u-1) + 384 * (u-1) ^ 2 + 388 * (z-4) + 708 * (z-4) * (u-1) +
      320 * (z-4) * (u-1) ^ 2 + 96 * (z-4) ^ 2 + 184 * (z-4) ^ 2 * (u-1) +
      88 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_seam_0: 9 terms; constant 416.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_seam_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) =
      416 + 928 * (u-1) + 512 * (u-1) ^ 2 + 200 * (z-4) + 456 * (z-4) * (u-1) +
      256 * (z-4) * (u-1) ^ 2 + 24 * (z-4) ^ 2 + 56 * (z-4) ^ 2 * (u-1) +
      32 * (z-4) ^ 2 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_peak_slack_0: 12 terms; constant 240.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_peak_slack_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 2 (2 * z * u) z (2 * z * u) 0-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 2 (2 * z * u) z (2 * z * u) 0-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 0) =
      240 + 368 * (u-1) + 128 * (u-1) ^ 2 + 252 * (z-4) + 444 * (z-4) * (u-1) +
      192 * (z-4) * (u-1) ^ 2 + 80 * (z-4) ^ 2 + 152 * (z-4) ^ 2 * (u-1) +
      72 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_seam_1: 16 terms; constant 414.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_seam_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) =
      414 + 1662 * (u-1) + 2016 * (u-1) ^ 2 + 768 * (u-1) ^ 3 + 344 * (z-4) +
      1360 * (z-4) * (u-1) + 1656 * (z-4) * (u-1) ^ 2 + 640 * (z-4) * (u-1) ^ 3 +
      92 * (z-4) ^ 2 + 364 * (z-4) ^ 2 * (u-1) + 448 * (z-4) ^ 2 * (u-1) ^ 2 +
      176 * (z-4) ^ 2 * (u-1) ^ 3 + 8 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      40 * (z-4) ^ 3 * (u-1) ^ 2 + 16 * (z-4) ^ 3 * (u-1) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_peak_slack_1: 15 terms; constant 746.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_peak_slack_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 2 (2 * z * u) z (2 * z * u) 1-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 2 (2 * z * u) z (2 * z * u) 1-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) =
      746 + 1674 * (u-1) + 1184 * (u-1) ^ 2 + 256 * (u-1) ^ 3 + 490 * (z-4) +
      1074 * (z-4) * (u-1) + 712 * (z-4) * (u-1) ^ 2 + 128 * (z-4) * (u-1) ^ 3 +
      108 * (z-4) ^ 2 + 228 * (z-4) ^ 2 * (u-1) + 136 * (z-4) ^ 2 * (u-1) ^ 2 +
      16 * (z-4) ^ 2 * (u-1) ^ 3 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_seam_1: 16 terms; constant 908.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_seam_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) =
      908 + 3404 * (u-1) + 4032 * (u-1) ^ 2 + 1536 * (u-1) ^ 3 + 724 * (z-4) +
      2756 * (z-4) * (u-1) + 3312 * (z-4) * (u-1) ^ 2 + 1280 * (z-4) * (u-1) ^ 3 +
      188 * (z-4) ^ 2 + 732 * (z-4) ^ 2 * (u-1) + 896 * (z-4) ^ 2 * (u-1) ^ 2 +
      352 * (z-4) ^ 2 * (u-1) ^ 3 + 16 * (z-4) ^ 3 + 64 * (z-4) ^ 3 * (u-1) +
      80 * (z-4) ^ 3 * (u-1) ^ 2 + 32 * (z-4) ^ 3 * (u-1) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_peak_slack_1: 15 terms; constant 1412.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_peak_slack_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 2 (2 * z * u) z (2 * z * u) 1-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 2 (2 * z * u) z (2 * z * u) 1-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 1) =
      1412 + 3268 * (u-1) + 2368 * (u-1) ^ 2 + 512 * (u-1) ^ 3 + 944 * (z-4) +
      2112 * (z-4) * (u-1) + 1424 * (z-4) * (u-1) ^ 2 + 256 * (z-4) * (u-1) ^ 3 +
      212 * (z-4) ^ 2 + 452 * (z-4) ^ 2 * (u-1) + 272 * (z-4) ^ 2 * (u-1) ^ 2 +
      32 * (z-4) ^ 2 * (u-1) ^ 3 + 16 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      16 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_seam_2: 12 terms; constant 504.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_seam_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) =
      504 + 1008 * (u-1) + 512 * (u-1) ^ 2 + 382 * (z-4) + 764 * (z-4) * (u-1) +
      384 * (z-4) * (u-1) ^ 2 + 96 * (z-4) ^ 2 + 192 * (z-4) ^ 2 * (u-1) +
      96 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_peak_slack_2: 6 terms; constant 44.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_peak_slack_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 2 (2 * z * u) z (2 * z * u) 2-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 2 (2 * z * u) z (2 * z * u) 2-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) =
      44 + 48 * (u-1) + 19 * (z-4) + 20 * (z-4) * (u-1) + 2 * (z-4) ^ 2 +
      2 * (z-4) ^ 2 * (u-1) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_seam_2: 12 terms; constant 1080.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_seam_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) =
      1080 + 2096 * (u-1) + 1024 * (u-1) ^ 2 + 798 * (z-4) + 1564 * (z-4) * (u-1) +
      768 * (z-4) * (u-1) ^ 2 + 196 * (z-4) ^ 2 + 388 * (z-4) ^ 2 * (u-1) +
      192 * (z-4) ^ 2 * (u-1) ^ 2 + 16 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      16 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_peak_slack_2: 4 terms; constant 12.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_peak_slack_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 2 (2 * z * u) z (2 * z * u) 2-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 2 (2 * z * u) z (2 * z * u) 2-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 2) =
      12 + 16 * (u-1) + 3 * (z-4) + 4 * (z-4) * (u-1) := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/old_seam_3: 0 terms; constant 0.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_seam_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 ≤ 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) =
      0 := by
    simp [oldSeam,newSeam]
  rw [hid] <;> positivity

-- corner_2/old_peak_slack_3: 12 terms; constant 296.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_old_peak_slack_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 2 (2 * z * u) z (2 * z * u) 3-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 2 (2 * z * u) z (2 * z * u) 3-1-2 * (oldSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) =
      296 + 552 * (u-1) + 256 * (u-1) ^ 2 + 210 * (z-4) + 402 * (z-4) * (u-1) +
      192 * (z-4) * (u-1) ^ 2 + 50 * (z-4) ^ 2 + 98 * (z-4) ^ 2 * (u-1) +
      48 * (z-4) ^ 2 * (u-1) ^ 2 + 4 * (z-4) ^ 3 + 8 * (z-4) ^ 3 * (u-1) +
      4 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_2/new_seam_3: 0 terms; constant 0.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_seam_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 ≤ 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) =
      0 := by
    simp [oldSeam,newSeam]
  rw [hid] <;> positivity

-- corner_2/new_peak_slack_3: 12 terms; constant 552.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_2_new_peak_slack_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 2 (2 * z * u) z (2 * z * u) 3-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 2 (2 * z * u) z (2 * z * u) 3-1-2 * (newSeam true 2 (2 * z * u) z (2 * z * u) (2-1) u 3) =
      552 + 1064 * (u-1) + 512 * (u-1) ^ 2 + 402 * (z-4) + 786 * (z-4) * (u-1) +
      384 * (z-4) * (u-1) ^ 2 + 98 * (z-4) ^ 2 + 194 * (z-4) ^ 2 * (u-1) +
      96 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_seam_0: 9 terms; constant 250.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_seam_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) =
      250 + 768 * (u-1) + 512 * (u-1) ^ 2 + 128 * (z-4) + 384 * (z-4) * (u-1) +
      256 * (z-4) * (u-1) ^ 2 + 16 * (z-4) ^ 2 + 48 * (z-4) ^ 2 * (u-1) +
      32 * (z-4) ^ 2 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_peak_slack_0: 12 terms; constant 1062.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_peak_slack_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 4 (2 * z * u) z (2 * z * u) 0-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 4 (2 * z * u) z (2 * z * u) 0-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) =
      1062 + 1824 * (u-1) + 768 * (u-1) ^ 2 + 776 * (z-4) + 1416 * (z-4) * (u-1) +
      640 * (z-4) * (u-1) ^ 2 + 192 * (z-4) ^ 2 + 368 * (z-4) ^ 2 * (u-1) +
      176 * (z-4) ^ 2 * (u-1) ^ 2 + 16 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      16 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_seam_0: 9 terms; constant 828.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_seam_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) =
      828 + 1856 * (u-1) + 1024 * (u-1) ^ 2 + 400 * (z-4) + 912 * (z-4) * (u-1) +
      512 * (z-4) * (u-1) ^ 2 + 48 * (z-4) ^ 2 + 112 * (z-4) ^ 2 * (u-1) +
      64 * (z-4) ^ 2 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_peak_slack_0: 12 terms; constant 484.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_peak_slack_0 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 4 (2 * z * u) z (2 * z * u) 0-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 4 (2 * z * u) z (2 * z * u) 0-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 0) =
      484 + 736 * (u-1) + 256 * (u-1) ^ 2 + 504 * (z-4) + 888 * (z-4) * (u-1) +
      384 * (z-4) * (u-1) ^ 2 + 160 * (z-4) ^ 2 + 304 * (z-4) ^ 2 * (u-1) +
      144 * (z-4) ^ 2 * (u-1) ^ 2 + 16 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      16 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_seam_1: 16 terms; constant 218.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_seam_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) =
      218 + 2206 * (u-1) + 3520 * (u-1) ^ 2 + 1536 * (u-1) ^ 3 + 264 * (z-4) +
      1912 * (z-4) * (u-1) + 2928 * (z-4) * (u-1) ^ 2 + 1280 * (z-4) * (u-1) ^ 3 +
      84 * (z-4) ^ 2 + 532 * (z-4) ^ 2 * (u-1) + 800 * (z-4) ^ 2 * (u-1) ^ 2 +
      352 * (z-4) ^ 2 * (u-1) ^ 3 + 8 * (z-4) ^ 3 + 48 * (z-4) ^ 3 * (u-1) +
      72 * (z-4) ^ 3 * (u-1) ^ 2 + 32 * (z-4) ^ 3 * (u-1) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_peak_slack_1: 15 terms; constant 2094.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_peak_slack_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 4 (2 * z * u) z (2 * z * u) 1-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 4 (2 * z * u) z (2 * z * u) 1-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) =
      2094 + 4458 * (u-1) + 2880 * (u-1) ^ 2 + 512 * (u-1) ^ 3 + 1402 * (z-4) +
      2954 * (z-4) * (u-1) + 1808 * (z-4) * (u-1) ^ 2 + 256 * (z-4) * (u-1) ^ 3 +
      316 * (z-4) ^ 2 + 652 * (z-4) ^ 2 * (u-1) + 368 * (z-4) ^ 2 * (u-1) ^ 2 +
      32 * (z-4) ^ 2 * (u-1) ^ 3 + 24 * (z-4) ^ 3 + 48 * (z-4) ^ 3 * (u-1) +
      24 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_seam_1: 16 terms; constant 680.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_seam_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) =
      680 + 4652 * (u-1) + 7040 * (u-1) ^ 2 + 3072 * (u-1) ^ 3 + 636 * (z-4) +
      3932 * (z-4) * (u-1) + 5856 * (z-4) * (u-1) ^ 2 + 2560 * (z-4) * (u-1) ^ 3 +
      180 * (z-4) ^ 2 + 1076 * (z-4) ^ 2 * (u-1) + 1600 * (z-4) ^ 2 * (u-1) ^ 2 +
      704 * (z-4) ^ 2 * (u-1) ^ 3 + 16 * (z-4) ^ 3 + 96 * (z-4) ^ 3 * (u-1) +
      144 * (z-4) ^ 3 * (u-1) ^ 2 + 64 * (z-4) ^ 3 * (u-1) ^ 3 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_peak_slack_1: 15 terms; constant 3944.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_peak_slack_1 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 4 (2 * z * u) z (2 * z * u) 1-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 4 (2 * z * u) z (2 * z * u) 1-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 1) =
      3944 + 8676 * (u-1) + 5760 * (u-1) ^ 2 + 1024 * (u-1) ^ 3 + 2696 * (z-4) +
      5800 * (z-4) * (u-1) + 3616 * (z-4) * (u-1) ^ 2 + 512 * (z-4) * (u-1) ^ 3 +
      620 * (z-4) ^ 2 + 1292 * (z-4) ^ 2 * (u-1) + 736 * (z-4) ^ 2 * (u-1) ^ 2 +
      64 * (z-4) ^ 2 * (u-1) ^ 3 + 48 * (z-4) ^ 3 + 96 * (z-4) ^ 3 * (u-1) +
      48 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_seam_2: 12 terms; constant 340.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_seam_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) =
      340 + 848 * (u-1) + 512 * (u-1) ^ 2 + 310 * (z-4) + 692 * (z-4) * (u-1) +
      384 * (z-4) * (u-1) ^ 2 + 88 * (z-4) ^ 2 + 184 * (z-4) ^ 2 * (u-1) +
      96 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_peak_slack_2: 12 terms; constant 720.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_peak_slack_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 4 (2 * z * u) z (2 * z * u) 2-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 4 (2 * z * u) z (2 * z * u) 2-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) =
      720 + 1232 * (u-1) + 512 * (u-1) ^ 2 + 475 * (z-4) + 860 * (z-4) * (u-1) +
      384 * (z-4) * (u-1) ^ 2 + 106 * (z-4) ^ 2 + 202 * (z-4) ^ 2 * (u-1) +
      96 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_seam_2: 12 terms; constant 916.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_seam_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) =
      916 + 1936 * (u-1) + 1024 * (u-1) ^ 2 + 726 * (z-4) + 1492 * (z-4) * (u-1) +
      768 * (z-4) * (u-1) ^ 2 + 188 * (z-4) ^ 2 + 380 * (z-4) ^ 2 * (u-1) +
      192 * (z-4) ^ 2 * (u-1) ^ 2 + 16 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      16 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_peak_slack_2: 12 terms; constant 1200.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_peak_slack_2 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 4 (2 * z * u) z (2 * z * u) 2-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 4 (2 * z * u) z (2 * z * u) 2-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 2) =
      1200 + 2224 * (u-1) + 1024 * (u-1) ^ 2 + 843 * (z-4) + 1612 * (z-4) * (u-1) +
      768 * (z-4) * (u-1) ^ 2 + 200 * (z-4) ^ 2 + 392 * (z-4) ^ 2 * (u-1) +
      192 * (z-4) ^ 2 * (u-1) ^ 2 + 16 * (z-4) ^ 3 + 32 * (z-4) ^ 3 * (u-1) +
      16 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/old_seam_3: 0 terms; constant 0.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_seam_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 ≤ 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) =
      0 := by
    simp [oldSeam,newSeam]
  rw [hid] <;> positivity

-- corner_4/old_peak_slack_3: 12 terms; constant 296.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_old_peak_slack_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < oldNext true 4 (2 * z * u) z (2 * z * u) 3-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : oldNext true 4 (2 * z * u) z (2 * z * u) 3-1-2 * (oldSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) =
      296 + 552 * (u-1) + 256 * (u-1) ^ 2 + 210 * (z-4) + 402 * (z-4) * (u-1) +
      192 * (z-4) * (u-1) ^ 2 + 50 * (z-4) ^ 2 + 98 * (z-4) ^ 2 * (u-1) +
      48 * (z-4) ^ 2 * (u-1) ^ 2 + 4 * (z-4) ^ 3 + 8 * (z-4) ^ 3 * (u-1) +
      4 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

-- corner_4/new_seam_3: 0 terms; constant 0.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_seam_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 ≤ 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : 2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) =
      0 := by
    simp [oldSeam,newSeam]
  rw [hid] <;> positivity

-- corner_4/new_peak_slack_3: 12 terms; constant 552.
set_option maxHeartbeats 1600000 in
private theorem cert_corner_4_new_peak_slack_3 (z u : ℤ) (hz : 4 ≤ z) (hu : 1 ≤ u) :
    0 < newNext true 4 (2 * z * u) z (2 * z * u) 3-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) := by
  have hZ : 0 ≤ z-4 := by omega
  have hT : 0 ≤ u-1 := by omega
  have hid : newNext true 4 (2 * z * u) z (2 * z * u) 3-1-2 * (newSeam true 4 (2 * z * u) z (2 * z * u) (4-1) u 3) =
      552 + 1064 * (u-1) + 512 * (u-1) ^ 2 + 402 * (z-4) + 786 * (z-4) * (u-1) +
      384 * (z-4) * (u-1) ^ 2 + 98 * (z-4) ^ 2 + 194 * (z-4) ^ 2 * (u-1) +
      96 * (z-4) ^ 2 * (u-1) ^ 2 + 8 * (z-4) ^ 3 + 16 * (z-4) ^ 3 * (u-1) +
      8 * (z-4) ^ 3 * (u-1) ^ 2 := by
    dsimp [oldSeam,newSeam,oldNext,newNext,delta,eps,width,E,A,B,L,M,D]
    norm_num <;> ring
  rw [hid] <;> positivity

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
