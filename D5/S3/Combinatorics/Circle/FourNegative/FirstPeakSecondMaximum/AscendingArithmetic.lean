/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/AscendingArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-construction)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Ascending arithmetic for the physical first-peak joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-! AscendingArithmetic for the paired physical source construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Ascending

private def D (y z : ℤ) : ℤ := y * z + y + 1
private def A (n y z t : ℤ) : ℤ := n * t * D y z + 1
private def B (n y t : ℤ) : ℤ := n * t ^ 2 * (y + 1) + t + 1
private def L (n z t : ℤ) : ℤ := n * z * t ^ 2 + z * t + z + 1
private def M (y z t : ℤ) : ℤ := t * y * z + D y z
private def delta (n y z t : ℤ) : ℤ := A n y z t-n * M y z t
private def E (n y z : ℤ) : ℤ := n * D y z
private def H (n y z t r v : ℤ) : ℤ := r * M y z t + v * A n y z t

-- equal/width: 18 monomials, constant 31.
set_option maxHeartbeats 1200000 in
private theorem cert_equal_width (n y t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (ht : 2 * y ≤ t) :
    0 < 2 * L n y t-B n y t-E n y y-2 * (M y y t + delta n y y t) := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hT : 0 ≤ t-2 * y := by omega
  have hid : 2 * L n y t-B n y t-E n y y-2 * (M y y t + delta n y y t) =
      31 + 
      51 * (t-2 * y) + 
      6 * (t-2 * y) ^ 2 + 
      88 * (y-4) + 
      38 * (y-4) * (t-2 * y) + 
      2 * (y-4) * (t-2 * y) ^ 2 + 
      36 * (y-4) ^ 2 + 
      6 * (y-4) ^ 2 * (t-2 * y) + 
      4 * (y-4) ^ 3 + 
      133 * (n-2) + 
      38 * (n-2) * (t-2 * y) + 
      3 * (n-2) * (t-2 * y) ^ 2 + 
      133 * (n-2) * (y-4) + 
      26 * (n-2) * (y-4) * (t-2 * y) + 
      1 * (n-2) * (y-4) * (t-2 * y) ^ 2 + 
      41 * (n-2) * (y-4) ^ 2 + 
      4 * (n-2) * (y-4) ^ 2 * (t-2 * y) + 
      4 * (n-2) * (y-4) ^ 3 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- equal/B-L: 12 monomials, constant 100.
set_option maxHeartbeats 1200000 in
private theorem cert_equal_cap (n y t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (ht : 2 * y ≤ t) :
    0 < B n y t-L n y t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hT : 0 ≤ t-2 * y := by omega
  have hid : B n y t-L n y t =
      100 + 
      29 * (t-2 * y) + 
      2 * (t-2 * y) ^ 2 + 
      49 * (y-4) + 
      7 * (y-4) * (t-2 * y) + 
      6 * (y-4) ^ 2 + 
      64 * (n-2) + 
      16 * (n-2) * (t-2 * y) + 
      1 * (n-2) * (t-2 * y) ^ 2 + 
      32 * (n-2) * (y-4) + 
      4 * (n-2) * (y-4) * (t-2 * y) + 
      4 * (n-2) * (y-4) ^ 2 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- twice/I: 24 monomials, constant 449.
set_option maxHeartbeats 1200000 in
private theorem cert_twice_I (n y f : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hf : 1 ≤ f) :
    0 < 2 * H n y (2 * y) (2 * y * f) n (f-1)-B n y (2 * y * f)-E n y (2 * y) := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hT : 0 ≤ f-1 := by omega
  have hid : 2 * H n y (2 * y) (2 * y * f) n (f-1)-B n y (2 * y * f)-E n y (2 * y) =
      449 + 
      922 * (f-1) + 
      544 * (f-1) ^ 2 + 
      352 * (y-4) + 
      710 * (y-4) * (f-1) + 
      392 * (y-4) * (f-1) ^ 2 + 
      92 * (y-4) ^ 2 + 
      184 * (y-4) ^ 2 * (f-1) + 
      96 * (y-4) ^ 2 * (f-1) ^ 2 + 
      8 * (y-4) ^ 3 + 
      16 * (y-4) ^ 3 * (f-1) + 
      8 * (y-4) ^ 3 * (f-1) ^ 2 + 
      229 * (n-2) + 
      464 * (n-2) * (f-1) + 
      272 * (n-2) * (f-1) ^ 2 + 
      177 * (n-2) * (y-4) + 
      356 * (n-2) * (y-4) * (f-1) + 
      196 * (n-2) * (y-4) * (f-1) ^ 2 + 
      46 * (n-2) * (y-4) ^ 2 + 
      92 * (n-2) * (y-4) ^ 2 * (f-1) + 
      48 * (n-2) * (y-4) ^ 2 * (f-1) ^ 2 + 
      4 * (n-2) * (y-4) ^ 3 + 
      8 * (n-2) * (y-4) ^ 3 * (f-1) + 
      4 * (n-2) * (y-4) ^ 3 * (f-1) ^ 2 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- twice/II: 18 monomials, constant 63.
set_option maxHeartbeats 1200000 in
private theorem cert_twice_II (n y f : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hf : 1 ≤ f) :
    0 < B n y (2 * y * f)-H n y (2 * y) (2 * y * f) n (f-1) := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hT : 0 ≤ f-1 := by omega
  have hid : B n y (2 * y * f)-H n y (2 * y) (2 * y * f) n (f-1) =
      63 + 
      183 * (f-1) + 
      48 * (f-1) ^ 2 + 
      32 * (y-4) + 
      94 * (y-4) * (f-1) + 
      28 * (y-4) * (f-1) ^ 2 + 
      4 * (y-4) ^ 2 + 
      12 * (y-4) ^ 2 * (f-1) + 
      4 * (y-4) ^ 2 * (f-1) ^ 2 + 
      27 * (n-2) + 
      88 * (n-2) * (f-1) + 
      24 * (n-2) * (f-1) ^ 2 + 
      15 * (n-2) * (y-4) + 
      46 * (n-2) * (y-4) * (f-1) + 
      14 * (n-2) * (y-4) * (f-1) ^ 2 + 
      2 * (n-2) * (y-4) ^ 2 + 
      6 * (n-2) * (y-4) ^ 2 * (f-1) + 
      2 * (n-2) * (y-4) ^ 2 * (f-1) ^ 2 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- twice/III: 17 monomials, constant 10.
set_option maxHeartbeats 1200000 in
private theorem cert_twice_III (n y f : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hf : 1 ≤ f) :
    0 < 4 * H n y (2 * y) (2 * y * f) n (f-1)-2 * L n (2 * y) (2 * y * f)-2 * E n y (2 * y) + 2 * y := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hT : 0 ≤ f-1 := by omega
  have hid : 4 * H n y (2 * y) (2 * y * f) n (f-1)-2 * L n (2 * y) (2 * y * f)-2 * E n y (2 * y) + 2 * y =
      10 + 
      196 * (f-1) + 
      320 * (f-1) ^ 2 + 
      2 * (y-4) + 
      80 * (y-4) * (f-1) + 
      144 * (y-4) * (f-1) ^ 2 + 
      8 * (y-4) ^ 2 * (f-1) + 
      16 * (y-4) ^ 2 * (f-1) ^ 2 + 
      74 * (n-2) + 
      160 * (n-2) * (f-1) + 
      160 * (n-2) * (f-1) ^ 2 + 
      34 * (n-2) * (y-4) + 
      72 * (n-2) * (y-4) * (f-1) + 
      72 * (n-2) * (y-4) * (f-1) ^ 2 + 
      4 * (n-2) * (y-4) ^ 2 + 
      8 * (n-2) * (y-4) ^ 2 * (f-1) + 
      8 * (n-2) * (y-4) ^ 2 * (f-1) ^ 2 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- twice/IV: 24 monomials, constant 511.
set_option maxHeartbeats 1200000 in
private theorem cert_twice_IV (n y f : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hf : 1 ≤ f) :
    0 < L n (2 * y) (2 * y * f)-H n y (2 * y) (2 * y * f) n (f-1) := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hT : 0 ≤ f-1 := by omega
  have hid : L n (2 * y) (2 * y * f)-H n y (2 * y) (2 * y * f) n (f-1) =
      511 + 
      1007 * (f-1) + 
      432 * (f-1) ^ 2 + 
      384 * (y-4) + 
      764 * (y-4) * (f-1) + 
      348 * (y-4) * (f-1) ^ 2 + 
      96 * (y-4) ^ 2 + 
      192 * (y-4) ^ 2 * (f-1) + 
      92 * (y-4) ^ 2 * (f-1) ^ 2 + 
      8 * (y-4) ^ 3 + 
      16 * (y-4) ^ 3 * (f-1) + 
      8 * (y-4) ^ 3 * (f-1) ^ 2 + 
      219 * (n-2) + 
      472 * (n-2) * (f-1) + 
      216 * (n-2) * (f-1) ^ 2 + 
      175 * (n-2) * (y-4) + 
      366 * (n-2) * (y-4) * (f-1) + 
      174 * (n-2) * (y-4) * (f-1) ^ 2 + 
      46 * (n-2) * (y-4) ^ 2 + 
      94 * (n-2) * (y-4) ^ 2 * (f-1) + 
      46 * (n-2) * (y-4) ^ 2 * (f-1) ^ 2 + 
      4 * (n-2) * (y-4) ^ 3 + 
      8 * (n-2) * (y-4) ^ 3 * (f-1) + 
      4 * (n-2) * (y-4) ^ 3 * (f-1) ^ 2 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- separated/width: 29 monomials, constant 207.
set_option maxHeartbeats 1200000 in
private theorem cert_separated_width (n y z t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : 4 * y ≤ z) (ht : z ≤ t) :
    0 < B n y t-E n y z-2 * (M y z t + delta n y z t) := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hZ : 0 ≤ z-4 * y := by omega
  have hT : 0 ≤ t-z := by omega
  have hid : B n y t-E n y z-2 * (M y z t + delta n y z t) =
      207 + 
      173 * (t-z) + 
      10 * (t-z) ^ 2 + 
      45 * (z-4 * y) + 
      12 * (z-4 * y) * (t-z) + 
      2 * (z-4 * y) ^ 2 + 
      116 * (y-4) + 
      76 * (y-4) * (t-z) + 
      2 * (y-4) * (t-z) ^ 2 + 
      12 * (y-4) * (z-4 * y) + 
      2 * (y-4) * (z-4 * y) * (t-z) + 
      16 * (y-4) ^ 2 + 
      8 * (y-4) ^ 2 * (t-z) + 
      1189 * (n-2) + 
      150 * (n-2) * (t-z) + 
      5 * (n-2) * (t-z) ^ 2 + 
      154 * (n-2) * (z-4 * y) + 
      10 * (n-2) * (z-4 * y) * (t-z) + 
      5 * (n-2) * (z-4 * y) ^ 2 + 
      857 * (n-2) * (y-4) + 
      70 * (n-2) * (y-4) * (t-z) + 
      1 * (n-2) * (y-4) * (t-z) ^ 2 + 
      71 * (n-2) * (y-4) * (z-4 * y) + 
      2 * (n-2) * (y-4) * (z-4 * y) * (t-z) + 
      1 * (n-2) * (y-4) * (z-4 * y) ^ 2 + 
      204 * (n-2) * (y-4) ^ 2 + 
      8 * (n-2) * (y-4) ^ 2 * (t-z) + 
      8 * (n-2) * (y-4) ^ 2 * (z-4 * y) + 
      16 * (n-2) * (y-4) ^ 3 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- separated/third: 38 monomials, constant 3173.
set_option maxHeartbeats 1200000 in
private theorem cert_separated_third (n y z t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : 4 * y ≤ z) (ht : z ≤ t) :
    0 < L n z t-2 * B n y t-E n y z := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hZ : 0 ≤ z-4 * y := by omega
  have hT : 0 ≤ t-z := by omega
  have hid : L n z t-2 * B n y t-E n y z =
      3173 + 
      398 * (t-z) + 
      12 * (t-z) ^ 2 + 
      919 * (z-4 * y) + 
      89 * (z-4 * y) * (t-z) + 
      2 * (z-4 * y) * (t-z) ^ 2 + 
      77 * (z-4 * y) ^ 2 + 
      4 * (z-4 * y) ^ 2 * (t-z) + 
      2 * (z-4 * y) ^ 3 + 
      2618 * (y-4) + 
      228 * (y-4) * (t-z) + 
      4 * (y-4) * (t-z) ^ 2 + 
      486 * (y-4) * (z-4 * y) + 
      24 * (y-4) * (z-4 * y) * (t-z) + 
      20 * (y-4) * (z-4 * y) ^ 2 + 
      712 * (y-4) ^ 2 + 
      32 * (y-4) ^ 2 * (t-z) + 
      64 * (y-4) ^ 2 * (z-4 * y) + 
      64 * (y-4) ^ 3 + 
      1467 * (n-2) + 
      192 * (n-2) * (t-z) + 
      6 * (n-2) * (t-z) ^ 2 + 
      444 * (n-2) * (z-4 * y) + 
      44 * (n-2) * (z-4 * y) * (t-z) + 
      1 * (n-2) * (z-4 * y) * (t-z) ^ 2 + 
      38 * (n-2) * (z-4 * y) ^ 2 + 
      2 * (n-2) * (z-4 * y) ^ 2 * (t-z) + 
      1 * (n-2) * (z-4 * y) ^ 3 + 
      1247 * (n-2) * (y-4) + 
      112 * (n-2) * (y-4) * (t-z) + 
      2 * (n-2) * (y-4) * (t-z) ^ 2 + 
      239 * (n-2) * (y-4) * (z-4 * y) + 
      12 * (n-2) * (y-4) * (z-4 * y) * (t-z) + 
      10 * (n-2) * (y-4) * (z-4 * y) ^ 2 + 
      348 * (n-2) * (y-4) ^ 2 + 
      16 * (n-2) * (y-4) ^ 2 * (t-z) + 
      32 * (n-2) * (y-4) ^ 2 * (z-4 * y) + 
      32 * (n-2) * (y-4) ^ 3 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- separated/L-B: 38 monomials, constant 5888.
set_option maxHeartbeats 1200000 in
private theorem cert_separated_cap (n y z t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : 4 * y ≤ z) (ht : z ≤ t) :
    0 < L n z t-B n y t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hZ : 0 ≤ z-4 * y := by omega
  have hT : 0 ≤ t-z := by omega
  have hid : L n z t-B n y t =
      5888 + 
      719 * (t-z) + 
      22 * (t-z) ^ 2 + 
      1248 * (z-4 * y) + 
      109 * (z-4 * y) * (t-z) + 
      2 * (z-4 * y) * (t-z) ^ 2 + 
      87 * (z-4 * y) ^ 2 + 
      4 * (z-4 * y) ^ 2 * (t-z) + 
      2 * (z-4 * y) ^ 3 + 
      4480 * (y-4) + 
      372 * (y-4) * (t-z) + 
      6 * (y-4) * (t-z) ^ 2 + 
      632 * (y-4) * (z-4 * y) + 
      28 * (y-4) * (z-4 * y) * (t-z) + 
      22 * (y-4) * (z-4 * y) ^ 2 + 
      1136 * (y-4) ^ 2 + 
      48 * (y-4) ^ 2 * (t-z) + 
      80 * (y-4) ^ 2 * (z-4 * y) + 
      96 * (y-4) ^ 3 + 
      2816 * (n-2) + 
      352 * (n-2) * (t-z) + 
      11 * (n-2) * (t-z) ^ 2 + 
      608 * (n-2) * (z-4 * y) + 
      54 * (n-2) * (z-4 * y) * (t-z) + 
      1 * (n-2) * (z-4 * y) * (t-z) ^ 2 + 
      43 * (n-2) * (z-4 * y) ^ 2 + 
      2 * (n-2) * (z-4 * y) ^ 2 * (t-z) + 
      1 * (n-2) * (z-4 * y) ^ 3 + 
      2176 * (n-2) * (y-4) + 
      184 * (n-2) * (y-4) * (t-z) + 
      3 * (n-2) * (y-4) * (t-z) ^ 2 + 
      312 * (n-2) * (y-4) * (z-4 * y) + 
      14 * (n-2) * (y-4) * (z-4 * y) * (t-z) + 
      11 * (n-2) * (y-4) * (z-4 * y) ^ 2 + 
      560 * (n-2) * (y-4) ^ 2 + 
      24 * (n-2) * (y-4) ^ 2 * (t-z) + 
      40 * (n-2) * (y-4) ^ 2 * (z-4 * y) + 
      48 * (n-2) * (y-4) ^ 3 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- general/w-cap: 56 monomials, constant 362.
set_option maxHeartbeats 1200000 in
private theorem cert_general_wcap (n y z t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : y ≤ z) (ht : z ≤ t) :
    0 < z * B n y t-2 * L n z t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hZ : 0 ≤ z-y := by omega
  have hT : 0 ≤ t-z := by omega
  have hid : z * B n y t-2 * L n z t =
      362 + 
      188 * (t-z) + 
      24 * (t-z) ^ 2 + 
      279 * (z-y) + 
      95 * (z-y) * (t-z) + 
      6 * (z-y) * (t-z) ^ 2 + 
      71 * (z-y) ^ 2 + 
      12 * (z-y) ^ 2 * (t-z) + 
      6 * (z-y) ^ 3 + 
      407 * (y-4) + 
      159 * (y-4) * (t-z) + 
      14 * (y-4) * (t-z) ^ 2 + 
      238 * (y-4) * (z-y) + 
      56 * (y-4) * (z-y) * (t-z) + 
      2 * (y-4) * (z-y) * (t-z) ^ 2 + 
      42 * (y-4) * (z-y) ^ 2 + 
      4 * (y-4) * (z-y) ^ 2 * (t-z) + 
      2 * (y-4) * (z-y) ^ 3 + 
      167 * (y-4) ^ 2 + 
      44 * (y-4) ^ 2 * (t-z) + 
      2 * (y-4) ^ 2 * (t-z) ^ 2 + 
      66 * (y-4) ^ 2 * (z-y) + 
      8 * (y-4) ^ 2 * (z-y) * (t-z) + 
      6 * (y-4) ^ 2 * (z-y) ^ 2 + 
      30 * (y-4) ^ 3 + 
      4 * (y-4) ^ 3 * (t-z) + 
      6 * (y-4) ^ 3 * (z-y) + 
      2 * (y-4) ^ 4 + 
      192 * (n-2) + 
      96 * (n-2) * (t-z) + 
      12 * (n-2) * (t-z) ^ 2 + 
      144 * (n-2) * (z-y) + 
      48 * (n-2) * (z-y) * (t-z) + 
      3 * (n-2) * (z-y) * (t-z) ^ 2 + 
      36 * (n-2) * (z-y) ^ 2 + 
      6 * (n-2) * (z-y) ^ 2 * (t-z) + 
      3 * (n-2) * (z-y) ^ 3 + 
      208 * (n-2) * (y-4) + 
      80 * (n-2) * (y-4) * (t-z) + 
      7 * (n-2) * (y-4) * (t-z) ^ 2 + 
      120 * (n-2) * (y-4) * (z-y) + 
      28 * (n-2) * (y-4) * (z-y) * (t-z) + 
      1 * (n-2) * (y-4) * (z-y) * (t-z) ^ 2 + 
      21 * (n-2) * (y-4) * (z-y) ^ 2 + 
      2 * (n-2) * (y-4) * (z-y) ^ 2 * (t-z) + 
      1 * (n-2) * (y-4) * (z-y) ^ 3 + 
      84 * (n-2) * (y-4) ^ 2 + 
      22 * (n-2) * (y-4) ^ 2 * (t-z) + 
      1 * (n-2) * (y-4) ^ 2 * (t-z) ^ 2 + 
      33 * (n-2) * (y-4) ^ 2 * (z-y) + 
      4 * (n-2) * (y-4) ^ 2 * (z-y) * (t-z) + 
      3 * (n-2) * (y-4) ^ 2 * (z-y) ^ 2 + 
      15 * (n-2) * (y-4) ^ 3 + 
      2 * (n-2) * (y-4) ^ 3 * (t-z) + 
      3 * (n-2) * (y-4) ^ 3 * (z-y) + 
      1 * (n-2) * (y-4) ^ 4 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

-- general/v-cap: 56 monomials, constant 378.
set_option maxHeartbeats 1200000 in
private theorem cert_general_vcap (n y z t : ℤ) (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : y ≤ z) (ht : z ≤ t) :
    0 < t * A n y z t-2 * L n z t := by
  have hN : 0 ≤ n-2 := by omega
  have hY : 0 ≤ y-4 := by omega
  have hZ : 0 ≤ z-y := by omega
  have hT : 0 ≤ t-z := by omega
  have hid : t * A n y z t-2 * L n z t =
      378 + 
      201 * (t-z) + 
      26 * (t-z) ^ 2 + 
      255 * (z-y) + 
      82 * (z-y) * (t-z) + 
      4 * (z-y) * (t-z) ^ 2 + 
      56 * (z-y) ^ 2 + 
      8 * (z-y) ^ 2 * (t-z) + 
      4 * (z-y) ^ 3 + 
      415 * (y-4) + 
      162 * (y-4) * (t-z) + 
      14 * (y-4) * (t-z) ^ 2 + 
      224 * (y-4) * (z-y) + 
      52 * (y-4) * (z-y) * (t-z) + 
      2 * (y-4) * (z-y) * (t-z) ^ 2 + 
      38 * (y-4) * (z-y) ^ 2 + 
      4 * (y-4) * (z-y) ^ 2 * (t-z) + 
      2 * (y-4) * (z-y) ^ 3 + 
      168 * (y-4) ^ 2 + 
      44 * (y-4) ^ 2 * (t-z) + 
      2 * (y-4) ^ 2 * (t-z) ^ 2 + 
      64 * (y-4) ^ 2 * (z-y) + 
      8 * (y-4) ^ 2 * (z-y) * (t-z) + 
      6 * (y-4) ^ 2 * (z-y) ^ 2 + 
      30 * (y-4) ^ 3 + 
      4 * (y-4) ^ 3 * (t-z) + 
      6 * (y-4) ^ 3 * (z-y) + 
      2 * (y-4) ^ 4 + 
      208 * (n-2) + 
      104 * (n-2) * (t-z) + 
      13 * (n-2) * (t-z) ^ 2 + 
      136 * (n-2) * (z-y) + 
      42 * (n-2) * (z-y) * (t-z) + 
      2 * (n-2) * (z-y) * (t-z) ^ 2 + 
      29 * (n-2) * (z-y) ^ 2 + 
      4 * (n-2) * (z-y) ^ 2 * (t-z) + 
      2 * (n-2) * (z-y) ^ 3 + 
      216 * (n-2) * (y-4) + 
      82 * (n-2) * (y-4) * (t-z) + 
      7 * (n-2) * (y-4) * (t-z) ^ 2 + 
      114 * (n-2) * (y-4) * (z-y) + 
      26 * (n-2) * (y-4) * (z-y) * (t-z) + 
      1 * (n-2) * (y-4) * (z-y) * (t-z) ^ 2 + 
      19 * (n-2) * (y-4) * (z-y) ^ 2 + 
      2 * (n-2) * (y-4) * (z-y) ^ 2 * (t-z) + 
      1 * (n-2) * (y-4) * (z-y) ^ 3 + 
      85 * (n-2) * (y-4) ^ 2 + 
      22 * (n-2) * (y-4) ^ 2 * (t-z) + 
      1 * (n-2) * (y-4) ^ 2 * (t-z) ^ 2 + 
      32 * (n-2) * (y-4) ^ 2 * (z-y) + 
      4 * (n-2) * (y-4) ^ 2 * (z-y) * (t-z) + 
      3 * (n-2) * (y-4) ^ 2 * (z-y) ^ 2 + 
      15 * (n-2) * (y-4) ^ 3 + 
      2 * (n-2) * (y-4) ^ 3 * (t-z) + 
      3 * (n-2) * (y-4) ^ 3 * (z-y) + 
      1 * (n-2) * (y-4) ^ 4 := by
    dsimp [H,delta,E,A,B,L,M,D]
    ring
  rw [hid]
  positivity

/- The literal finite-grid rule. Every division is Euclidean division in Int. -/
private def gridV (A M cap : ℤ) : ℤ := (cap-M)/A
private def gridR (n A M cap : ℤ) : ℤ := min n ((cap-gridV A M cap * A)/M)

private theorem grid (n A M δ cap : ℤ)
    (hn : 1 ≤ n) (hM : 0<M) (hδ : 0 ≤ δ) (hA : A=n * M + δ) (hcap : M ≤ cap) :
    let v := gridV A M cap
    let r := gridR n A M cap
    0 ≤ v ∧ 1 ≤ r ∧ r ≤ n ∧ r * M + v * A ≤ cap ∧ 
      0 ≤ cap-(r * M + v * A) ∧ cap-(r * M + v * A)<M + δ := by
  dsimp only
  have hnM : M ≤ n * M := by
    have hm := mul_le_mul_of_nonneg_right hn hM.le
    simpa only [one_mul] using hm
  have hA0 : 0<A := by omega
  let v := gridV A M cap
  let u := cap-v * A
  let s := u/M
  have hv : 0 ≤ v := Int.ediv_nonneg (by omega) hA0.le
  have hmodA := Int.emod_add_mul_ediv (cap-M) A
  have hmodA0 := Int.emod_nonneg (cap-M) (ne_of_gt hA0)
  have hmodAlt := Int.emod_lt_of_pos (cap-M) hA0
  have hu : M ≤ u ∧ u<M + A := by
    dsimp [u,v,gridV]
    constructor <;> nlinarith only [hmodA,hmodA0,hmodAlt]
  have hmodM := Int.emod_add_mul_ediv u M
  have hmodM0 := Int.emod_nonneg u (ne_of_gt hM)
  have hmodMlt := Int.emod_lt_of_pos u hM
  have hs : 1 ≤ s := by
    by_contra hs
    have hm : s * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hM.le
    dsimp [s] at hm
    nlinarith only [hu.1,hmodM,hmodMlt,hm]
  have hr1 : 1 ≤ min n s := le_min hn hs
  have hrn : min n s ≤ n := min_le_left _ _
  have hrs : min n s ≤ s := min_le_right _ _
  have hH : min n s * M + v * A ≤ cap := by
    have hm := mul_le_mul_of_nonneg_right hrs hM.le
    dsimp [s,u] at hm hmodM hmodM0
    nlinarith only [hm,hmodM,hmodM0]
  have hgap : cap-(min n s * M + v * A)<M + δ := by
    by_cases hsn : s ≤ n
    · rw [min_eq_right hsn]
      dsimp [s,u] at hmodM hmodMlt
      nlinarith only [hmodM,hmodMlt,hδ]
    · rw [min_eq_left (by omega : n ≤ s)]
      dsimp [u] at hu
      nlinarith only [hu.2,hA]
  change 0 ≤ v ∧ 1 ≤ min n s ∧ min n s ≤ n ∧ min n s * M + v * A ≤ cap ∧ 
    0 ≤ cap-(min n s * M + v * A) ∧ cap-(min n s * M + v * A)<M + δ
  exact ⟨hv,hr1,hrn,hH,by omega,hgap⟩

private theorem grid_capacity (n y z t cap : ℤ)
    (hA : 0<A n y z t) (hM : 0<M y z t)
    (hcap : M y z t ≤ cap) (hL : cap ≤ L n z t)
    (hwide : 2 * L n z t<t * A n y z t) :
    2 * gridV (A n y z t) (M y z t) cap<t := by
  let v := gridV (A n y z t) (M y z t) cap
  have he := Int.emod_add_mul_ediv (cap-M y z t) (A n y z t)
  have hr := Int.emod_nonneg (cap-M y z t) (ne_of_gt hA)
  have hvA : v * A n y z t ≤ cap-M y z t := by
    dsimp [v,gridV]
    nlinarith only [he,hr]
  change 2 * v<t
  by_contra h
  have ht : t ≤ 2 * v := by omega
  have hm := mul_le_mul_of_nonneg_right ht hA.le
  nlinarith only [hvA,hL,hwide,hM,hm]

/- These are the four exact allocation inequalities, with literal binary capacities. -/
private def Allocation (n y z t r v w : ℤ) : Prop :=
  1 ≤ r ∧ r ≤ n ∧ 0 ≤ v ∧ 2 * v<t ∧ 0 ≤ w ∧ 2 * w<z ∧ 
  B n y t + r * D y z ≤ 2 * H n y z t r v ∧ H n y z t r v ≤ B n y t ∧ 
  2 * L n z t + 2 * r * D y z-z ≤ 4 * H n y z t r v + 2 * (2 * B n y t-1) * w ∧ 
  H n y z t r v + B n y t * w ≤ L n z t

private theorem parameter_bounds (n y z t : ℤ)
    (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : y ≤ z) (ht : z ≤ t) (hty : 2 * y ≤ t) :
    0<A n y z t ∧ 0<B n y t ∧ 0<M y z t ∧ 
      z + 1 ≤ D y z ∧ 0<delta n y z t ∧ 
      0 ≤ 2 * A n y z t-n * (2 * M y z t-D y z) ∧ 
      2 * (2 * A n y z t-n * (2 * M y z t-D y z)) ≤ A n y z t-1 := by
  have hz0 : 4 ≤ z := by omega
  have ht0 : 4 ≤ t := by omega
  have hn0 : 0<n := by omega
  have hy0 : 0<y := by omega
  have hzpos : 0<z := by omega
  have htpos : 0<t := by omega
  have hyz4 := mul_le_mul_of_nonneg_right hy hzpos.le
  have hD : 21 ≤ D y z := by dsimp [D]; nlinarith only [hyz4,hy,hz0]
  have hDz : z + 1 ≤ D y z := by dsimp [D]; nlinarith only [hyz4,hy,hz0]
  have hDpos : 0<D y z := by omega
  have hA : 0<A n y z t := by dsimp [A]; positivity
  have hB : 0<B n y t := by dsimp [B]; positivity
  have hM : 0<M y z t := by dsimp [M]; positivity
  have hδid : delta n y z t = n * (y * (t-z) + (t-y)-1) + 1 := by
    dsimp [delta,A,M,D]; ring
  have hprod : 0 ≤ y * (t-z) := mul_nonneg (by omega) (by omega)
  have hδ : 0<delta n y z t := by
    rw [hδid]
    have hi : 0 ≤ y * (t-z) + (t-y)-1 := by omega
    have hm := mul_nonneg hn0.le hi
    omega
  have hid : A n y z t-1-2 * (2 * A n y z t-n * (2 * M y z t-D y z)) =
      n * (t * (y * (z-3)-3) + 2 * D y z)-4 := by
    dsimp [A,M,D]; ring
  have hyz : 1 ≤ y * (z-3)-3 := by
    have hm := mul_le_mul_of_nonneg_right hy (show 0 ≤ z-3 by omega)
    nlinarith only [hm,hz0]
  have hslack : 0 ≤ A n y z t-1-2 * (2 * A n y z t-n * (2 * M y z t-D y z)) := by
    rw [hid]
    have htp : t ≤ t * (y * (z-3)-3) := by
      simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hyz htpos.le
    have hi : 4 ≤ t * (y * (z-3)-3) + 2 * D y z := by omega
    have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ t * (y * (z-3)-3) + 2 * D y z by omega)
    nlinarith only [hi,hm]
  have hK : 2 * A n y z t-n * (2 * M y z t-D y z)=2 * delta n y z t + E n y z := by
    dsimp [delta,E]; ring
  have hE0 : 0 ≤ E n y z := by
    dsimp [E]
    exact mul_nonneg hn0.le (by omega)
  exact ⟨hA,hB,hM,hDz,hδ,by nlinarith only [hK,hδ,hE0],by omega⟩

private theorem allocate_equal (n y t : ℤ)
    (hn : 2 ≤ n) (hy : 4 ≤ y) (ht : 2 * y ≤ t) :
    ∃ r v w : ℤ, Allocation n y y t r v w := by
  obtain ⟨hA,hB,hM,hD,hδ,_,_⟩ := parameter_bounds n y y t hn hy le_rfl (by omega) ht
  have hw := cert_equal_width n y t hn hy ht
  have hc := cert_equal_cap n y t hn hy ht
  have hwide := cert_general_vcap n y y t hn hy le_rfl (by omega)
  have hE : 0 ≤ E n y y := by
    dsimp [E]
    exact mul_nonneg (by omega) (by omega)
  have hcap : M y y t ≤ L n y t := by nlinarith
  let v := gridV (A n y y t) (M y y t) (L n y t)
  let r := gridR n (A n y y t) (M y y t) (L n y t)
  obtain ⟨hv,hr,hrn,hH,_,hgap⟩ := grid n (A n y y t) (M y y t)
    (delta n y y t) (L n y t) (by omega) hM hδ.le (by dsimp [delta]; ring) hcap
  change 0 ≤ v at hv
  change 1 ≤ r at hr
  change r ≤ n at hrn
  change H n y y t r v ≤ L n y t at hH
  change L n y t-H n y y t r v<M y y t + delta n y y t at hgap
  have hvCap := grid_capacity n y y t (L n y t) hA hM hcap le_rfl (by omega)
  have hrD : r * D y y ≤ E n y y := by
    dsimp [E]
    exact mul_le_mul_of_nonneg_right hrn (by omega)
  have hI : B n y t + r * D y y ≤ 2 * H n y y t r v := by
    nlinarith only [hw,hgap,hrD]
  refine ⟨r,v,0,hr,hrn,hv,hvCap,le_rfl,by omega,hI,?_,?_,?_⟩
  · omega
  · have : L n y t ≤ B n y t := by omega
    dsimp [H] at hI ⊢
    dsimp [E] at hrD
    nlinarith only [hI,hw,hδ.le,hM.le,hrD,this,hy]
  · simpa [H] using hH

private theorem allocate_twice (n y z t f : ℤ)
    (hn : 2 ≤ n) (hy : 4 ≤ y) (hf : 1 ≤ f) (hz : z=2 * y) (ht : t=z * f) :
    Allocation n y z t n (f-1) 0 := by
  subst z
  subst t
  have hI := cert_twice_I n y f hn hy hf
  have hII := cert_twice_II n y f hn hy hf
  have hIII := cert_twice_III n y f hn hy hf
  have hIV := cert_twice_IV n y f hn hy hf
  have hvCap : 2 * (f-1)<2 * y * f := by
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ y by omega) (show 0 ≤ f by omega)
    nlinarith only [hm]
  dsimp [Allocation,E] at * 
  exact ⟨by omega,le_rfl,by omega,hvCap,le_rfl,by omega,
    by omega,by omega,by simpa using (show 2 * L n (2 * y) (2 * y * f) + 2 * n * D y (2 * y)-2 * y ≤ 
      4 * H n y (2 * y) (2 * y * f) n (f-1) by nlinarith only [hIII]),by nlinarith only [hIV]⟩

private theorem allocate_separated (n y z t : ℤ)
    (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : 4 * y ≤ z) (ht : z ≤ t) :
    ∃ r v w : ℤ, Allocation n y z t r v w := by
  have hyz : y ≤ z := by omega
  obtain ⟨hA,hB,hM,hD,hδ,_,_⟩ :=
    parameter_bounds n y z t hn hy hyz ht (by omega)
  have hwidth := cert_separated_width n y z t hn hy hz ht
  have hthird := cert_separated_third n y z t hn hy hz ht
  have hcapL := cert_separated_cap n y z t hn hy hz ht
  have hvcap := cert_general_vcap n y z t hn hy hyz ht
  have hwcap := cert_general_wcap n y z t hn hy hyz ht
  have hE : 0 ≤ E n y z := by
    dsimp [E]
    exact mul_nonneg (by omega) (by omega)
  have hcap : M y z t ≤ B n y t := by nlinarith
  let v := gridV (A n y z t) (M y z t) (B n y t)
  let r := gridR n (A n y z t) (M y z t) (B n y t)
  obtain ⟨hv,hr,hrn,hH,_,hgap⟩ := grid n (A n y z t) (M y z t)
    (delta n y z t) (B n y t) (by omega) hM hδ.le (by dsimp [delta]; ring) hcap
  change 0 ≤ v at hv
  change 1 ≤ r at hr
  change r ≤ n at hrn
  change H n y z t r v ≤ B n y t at hH
  change B n y t-H n y z t r v<M y z t + delta n y z t at hgap
  have hvCap := grid_capacity n y z t (B n y t) hA hM hcap (by omega) (by omega)
  have hrD : r * D y z ≤ E n y z := by
    dsimp [E]
    exact mul_le_mul_of_nonneg_right hrn (by omega)
  have hI : B n y t + r * D y z ≤ 2 * H n y z t r v := by
    nlinarith only [hgap,hwidth,hrD]
  have hHL : H n y z t r v ≤ L n z t := by omega
  let w := (L n z t-H n y z t r v)/B n y t
  have hw : 0 ≤ w := Int.ediv_nonneg (by omega) hB.le
  have he := Int.emod_add_mul_ediv (L n z t-H n y z t r v) (B n y t)
  have he0 := Int.emod_nonneg (L n z t-H n y z t r v) (ne_of_gt hB)
  have helt := Int.emod_lt_of_pos (L n z t-H n y z t r v) hB
  have hrest : 0 ≤ L n z t-H n y z t r v-B n y t * w ∧ 
      L n z t-H n y z t r v-B n y t * w ≤ B n y t-1 := by
    dsimp [w]; constructor <;> nlinarith only [he,he0,helt]
  have hH0 : 0 ≤ H n y z t r v := by
    dsimp [H]
    exact add_nonneg (mul_nonneg (by omega) hM.le) (mul_nonneg hv hA.le)
  have hwCap : 2 * w<z := by
    by_contra h
    have hzW : z ≤ 2 * w := by omega
    have hm := mul_le_mul_of_nonneg_left hzW hB.le
    nlinarith only [hm,hrest.1,hwcap,hH0]
  have hIII : 2 * L n z t + 2 * r * D y z-z ≤ 
      4 * H n y z t r v + 2 * (2 * B n y t-1) * w := by
    nlinarith only [hrest.2,hrD,hthird,hwCap]
  exact ⟨r,v,w,hr,hrn,hv,hvCap,hw,hwCap,hI,hH,hIII,by omega⟩

/- Exhaustive dyadic branch selection, including both unbounded adjacent faces. -/
private theorem allocate_dyadic (a b c d : ℕ)
    (hb : 2 ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hda : d<a)
    (hne : ¬(b=c ∧ c=d)) :
    ∃ r v w : ℤ, Allocation ((2:ℤ) ^ (a-d)) (2 ^ b) (2 ^ c) (2 ^ d) r v w := by
  have hn : (2:ℤ) ≤ 2 ^ (a-d) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show 1 ≤ a-d by omega)
  have hy : (4:ℤ) ≤ 2 ^ b := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hb
  have hbd : b<d := by omega
  have hty : 2 * (2:ℤ) ^ b ≤ 2 ^ d := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show b + 1 ≤ d by omega)
    simpa [pow_succ,mul_comm] using hp
  by_cases he : c=b
  · subst c
    exact allocate_equal _ _ _ hn hy hty
  · by_cases ht : c=b + 1
    · let f : ℤ := 2 ^ (d-c)
      have hf : 1 ≤ f := by dsimp [f]; exact_mod_cast Nat.one_le_two_pow
      have hz : (2:ℤ) ^ c=2 * 2 ^ b := by rw [ht,pow_succ]; ring
      have htf : (2:ℤ) ^ d=2 ^ c * f := by
        dsimp [f]
        rw [←pow_add]
        congr 1
        omega
      exact ⟨_,_,_,allocate_twice _ _ _ _ f hn hy hf hz htf⟩
    · have hz : 4 * (2:ℤ) ^ b ≤ 2 ^ c := by
        have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) (show b + 2 ≤ c by omega)
        simpa [pow_add,mul_comm] using hp
      have hzt : (2:ℤ) ^ c ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hcd
      exact allocate_separated _ _ _ _ hn hy hz hzt

/- Actual matching successor gates for terminal order X,U,V,W. -/
private theorem gates (n y z t r v w : ℤ)
    (hn : 2 ≤ n) (hy : 4 ≤ y) (hz : y ≤ z) (ht : z ≤ t) (hty : 2 * y ≤ t)
    (ha : Allocation n y z t r v w) :
    let S0 := A n y z t-n * M y z t
    let S1 := B n y t-H n y z t r v
    let S2 := L n z t-H n y z t r v-B n y t * w
    let K0 := 2 * A n y z t-n * (2 * M y z t-D y z)
    let K1 := (2 * B n y t-1)-r * (2 * M y z t-D y z)-2 * v * A n y z t
    let K2 := (2 * L n z t-z-1)-r * (2 * M y z t-D y z)-2 * v * A n y z t-w * (2 * B n y t-1)
    0 ≤ S0 ∧ 2 * S0 ≤ A n y z t-1 ∧ 0 ≤ K0 ∧ 2 * K0 ≤ A n y z t-1 ∧ 
    0 ≤ S1 ∧ 2 * S1 ≤ B n y t-1 ∧ 0 ≤ K1 ∧ 2 * K1 ≤ (2 * B n y t-1)-1 ∧ 
    0 ≤ S2 ∧ 2 * S2 ≤ L n z t-1 ∧ 0 ≤ K2 ∧ 2 * K2 ≤ (2 * L n z t-z-1)-1 := by
  obtain ⟨hA,hB,hM,hD,hδ,hK0,hK0p⟩ := parameter_bounds n y z t hn hy hz ht hty
  obtain ⟨hr,hrn,hv,hvc,hw,hwc,hI,hII,hIII,hIV⟩ := ha
  have hΓ : z + 1 ≤ r * D y z := by
    have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ D y z by omega)
    nlinarith only [hm,hD]
  have hE : 0 ≤ E n y z := by
    dsimp [E]
    exact mul_nonneg (by omega) (by omega)
  have e0 : 2 * A n y z t-n * (2 * M y z t-D y z)=2 * delta n y z t + E n y z := by
    dsimp [delta,E]; ring
  have e1 : (2 * B n y t-1)-r * (2 * M y z t-D y z)-2 * v * A n y z t =
      2 * (B n y t-H n y z t r v) + r * D y z-1 := by dsimp [H]; ring
  have e2 : (2 * L n z t-z-1)-r * (2 * M y z t-D y z)-2 * v * A n y z t-w * (2 * B n y t-1) =
      2 * (L n z t-H n y z t r v-B n y t * w) + r * D y z + w-z-1 := by dsimp [H]; ring
  have hz4 : 4 ≤ z := by omega
  have hΓpos : 1 ≤ r * D y z := by omega
  dsimp only
  change 0 ≤ delta n y z t ∧ 2 * delta n y z t ≤ _ ∧ _
  refine ⟨hδ.le,by nlinarith only [e0,hE,hK0p,hδ.le],hK0,hK0p,
    by omega,by nlinarith only [hI,hΓpos],by rw [e1]; omega,?_,
    by omega,?_,by rw [e2]; omega,?_⟩
  · rw [e1]; nlinarith only [hI]
  · have : 0 ≤ r * D y z + w-z-1 := by omega
    nlinarith only [hIII,this,hΓ,hw,hz4]
  · rw [e2]; nlinarith only [hIII]

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Ascending
