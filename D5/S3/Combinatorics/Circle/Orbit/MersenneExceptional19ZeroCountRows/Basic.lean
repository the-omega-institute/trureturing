/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroCountRows/Basic
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Universal exceptional19 five-floor row classification and exact cardinalities. -/
module
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic
public import Batteries.Tactic.OpenPrivate
/-! # Common definitions and universal floor bound for exceptional19 rows -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
open scoped BigOperators
private def L (m : ℕ) : ℕ := 152 * m-9
/- All three arguments are Nat; all field arithmetic is explicitly Rat. -/
private def rowB (m : ℕ) : ℚ := (152 : ℚ) * (m : ℚ) - 8
private def X (m v u : ℕ) : ℚ :=
  ((19 : ℚ) * (u : ℚ) + (v : ℚ)) / (19 * rowB m)
private def Z (m v u : ℕ) : ℚ :=
  (v : ℚ) / 19 + X m v u * (1 + 1 / rowB m)
private def Hjump (z : ℚ) : ℤ := ⌊8 * z⌋ - ⌊4 * z⌋ + ⌊z⌋
private def rowValue (m v u : ℕ) : ℤ :=
  -⌊(5 : ℚ) * (v : ℚ) / 19 + 2 * X m v u⌋ + Hjump (Z m v u) -
    ⌊4 * X m v u * (1 + 1 / rowB m + 1 / rowB m ^ 2)⌋
private def rowZeroCount (m v : ℕ) : ℕ :=
  ((Finset.range (L m)).filter (fun u => rowValue m v u = 0)).card

/-- The same five floors, with common positive integer denominators. -/
private def normalizedRow (b u v : ℤ) : ℤ :=
  -( (38 * u + (5 * b + 2) * v) / (19 * b))  +
    (152 * (b + 1) * u + 8 * v * (b^2 + b + 1))/(19 * b^2) -
    (76 * (b + 1) * u + 4 * v * (b^2 + b + 1))/(19 * b^2)  +
    (19 * (b + 1) * u + v * (b^2 + b + 1))/(19 * b^2) -
    (76 * (b^2 + b + 1) * u + 4 * v * (b^2 + b + 1))/(19 * b^3)

private theorem rowValue_normalized (m v u : ℕ) (hm : 27 ≤ m) :
    rowValue m v u = normalizedRow (152 * (m:ℤ)-8) u v := by
  let b : ℤ := 152 * (m:ℤ)-8
  have hb : 0 < b := by dsimp [b]; omega
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hrow : rowB m = (b : ℚ) := by simp [rowB,b]
  have hf (a c : ℤ) (hc : 0 ≤ c) : ⌊(a : ℚ)/(c : ℚ)⌋ = a/c := by
    rw [Int.floor_div_cast_of_nonneg hc,Int.floor_intCast]
  have ha : (5:ℚ) * v/19 + 2 * X m v u =
      ((38 * (u:ℤ) + (5 * b + 2) * v : ℤ) : ℚ) / ((19 * b : ℤ) : ℚ) := by
    dsimp [X]
    rw [hrow]
    push_cast
    field_simp
    <;> ring
  have hz (a : ℤ) : (a : ℚ) * Z m v u =
      ((19 * a * (b + 1) * u + a * v * (b^2 + b + 1) : ℤ) : ℚ)/((19 * b^2 : ℤ) : ℚ) := by
    dsimp [Z,X]
    rw [hrow]
    push_cast
    field_simp
    <;> ring
  have hc : 4 * X m v u * (1 + 1/rowB m + 1/rowB m^2) =
      ((76 * (b^2 + b + 1) * u + 4 * v * (b^2 + b + 1) : ℤ) : ℚ)/((19 * b^3 : ℤ) : ℚ) := by
    dsimp [X]
    rw [hrow]
    push_cast
    field_simp
    <;> ring
  have hz8 := hz 8
  have hz4 := hz 4
  have hz1 := hz 1
  norm_num only [Int.cast_ofNat,Int.cast_one,one_mul] at hz8 hz4 hz1
  dsimp [rowValue,Hjump]
  rw [ha,hz8,hz4,hz1,hc]
  rw [hf _ _ (by positivity),hf _ _ (by positivity),hf _ _ (by positivity),
    hf _ _ (by positivity),hf _ _ (by positivity)]
  norm_num [normalizedRow,b]
  <;> ring

/-- Endpoint certificates imply a floor value on every integer in the cell. -/
private theorem floor_on_cell (a b c l h z u : ℤ)
    (hc : 0 < c) (ha : 0 ≤ a)
    (hlo : z * c ≤ a * l + b) (hhi : a * (h-1) + b < (z + 1) * c)
    (hu : l ≤ u ∧ u < h) : (a * u + b)/c=z := by
  apply (Int.ediv_eq_iff_of_pos hc).mpr
  have hleft := mul_nonneg ha (sub_nonneg.mpr hu.1)
  have hright := mul_nonneg ha (show 0 ≤ h-1-u by omega)
  constructor <;> nlinarith only [hlo,hhi,hleft,hright]


end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroCountRows
