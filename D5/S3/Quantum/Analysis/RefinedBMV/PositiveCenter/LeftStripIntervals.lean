/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripIntervals
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rounded interval arithmetic and Horner enclosures for the left-strip certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Box

/-! Outward-rounded dyadic intervals for the left-strip enclosure. -/

namespace RefinedBMV.PositiveCenter.SmallCorner

open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open RefinedBMV.FourSpectrumLift (sqrt_box_of_square_bounds)

set_option autoImplicit false

private abbrev Bounds := ℚ × ℚ

private def Encloses (a : Bounds) (x : ℝ) : Prop :=
  (a.1 : ℝ) ≤ x ∧ x ≤ (a.2 : ℝ)

private def point (x : ℚ) : Bounds := (x, x)
private def add (a b : Bounds) : Bounds := (a.1 + b.1, a.2 + b.2)
private def neg (a : Bounds) : Bounds := (-a.2, -a.1)
private def sub (a b : Bounds) : Bounds := add a (neg b)
private def grid : ℚ := 17592186044416
private def down (x : ℚ) : ℚ := (⌊x * grid⌋ : ℤ) / grid
private def up (x : ℚ) : ℚ := -down (-x)

private theorem down_le (x : ℚ) : down x ≤ x := by
  rw [down, div_le_iff₀ (by norm_num [grid])]
  exact Int.floor_le _

private theorem le_up (x : ℚ) : x ≤ up x := by
  simpa [up] using neg_le_neg (down_le (-x))

private def mul (a b : Bounds) : Bounds :=
  let p := a.1 * b.1
  let q := a.1 * b.2
  let r := a.2 * b.1
  let s := a.2 * b.2
  (down (min (min p q) (min r s)), up (max (max p q) (max r s)))

private theorem encloses_point (x : ℚ) : Encloses (point x) (x : ℝ) :=
  ⟨le_rfl, le_rfl⟩

private theorem encloses_add {a b : Bounds} {x y : ℝ}
    (hx : Encloses a x) (hy : Encloses b y) : Encloses (add a b) (x + y) := by
  simpa only [Encloses, add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

private theorem encloses_neg {a : Bounds} {x : ℝ} (hx : Encloses a x) :
    Encloses (neg a) (-x) := by
  simpa only [Encloses, neg, Rat.cast_neg] using
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

private theorem encloses_sub {a b : Bounds} {x y : ℝ}
    (hx : Encloses a x) (hy : Encloses b y) : Encloses (sub a b) (x - y) := by
  rw [sub_eq_add_neg]
  exact encloses_add hx (encloses_neg hy)

private theorem encloses_ordered {a : Bounds} {x : ℝ} (hx : Encloses a x) : a.1 ≤ a.2 :=
  Rat.cast_le.mp (hx.1.trans hx.2)

private theorem encloses_mul {a b : Bounds} {x y : ℝ}
    (hx : Encloses a x) (hy : Encloses b y) : Encloses (mul a b) (x * y) := by
  let box : Fin 2 → Bounds := ![a, b]
  let args : Fin 2 → ℝ := ![x, y]
  let e : Expr 2 := .mul (mul a b).1 (mul a b).2
    (.input 0 a.1 a.2) (.input 1 b.1 b.2)
  have hb : ∀ i, Encloses (box i) (args i) := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have ha := encloses_ordered hx
  have hc := encloses_ordered hy
  have hcheck : check box e = true := by
    unfold e
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · simp [check, box, ha]
    · simp [check, box, hc]
    apply decide_eq_true
    have hlo (p q r s : ℚ) := down_le (min (min p q) (min r s))
    have hhi (p q r s : ℚ) := le_up (max (max p q) (max r s))
    dsimp only [mul]
    have h₁ := (hlo (a.1*b.1) (a.1*b.2) (a.2*b.1) (a.2*b.2)).trans
      ((min_le_left _ _).trans (min_le_left _ _))
    have h₂ := (hhi (a.1*b.1) (a.1*b.2) (a.2*b.1) (a.2*b.2))
    have hp := ((le_max_left _ _).trans (le_max_left _ _)).trans h₂
    exact ⟨h₁.trans hp, h₁,
      (down_le _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (down_le _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (down_le _).trans ((min_le_right _ _).trans (min_le_right _ _)), hp,
      ((le_max_right _ _).trans (le_max_left _ _)).trans h₂,
      ((le_max_left _ _).trans (le_max_right _ _)).trans h₂,
      ((le_max_right _ _).trans (le_max_right _ _)).trans h₂⟩
  exact checked_expression_encloses box args hb e hcheck

private def clampLo (a : Bounds) (l : ℚ) : Bounds := (max l a.1, a.2)
private def clampHi (a : Bounds) (u : ℚ) : Bounds := (a.1, min u a.2)

private theorem encloses_clampLo {a : Bounds} {x : ℝ} {l : ℚ}
    (hx : Encloses a x) (hl : (l : ℝ) ≤ x) : Encloses (clampLo a l) x := by
  simpa only [Encloses, clampLo, Rat.cast_max] using And.intro (max_le hl hx.1) hx.2

private theorem encloses_clampHi {a : Bounds} {x : ℝ} {u : ℚ}
    (hx : Encloses a x) (hu : x ≤ (u : ℝ)) : Encloses (clampHi a u) x := by
  simpa only [Encloses, clampHi, Rat.cast_min] using And.intro hx.1 (le_min hu hx.2)

private def inv (a : Bounds) : Bounds := (down (1 / a.2), up (1 / max (1/64) a.1))

private theorem encloses_inv {a : Bounds} {x : ℝ} (hx : Encloses a x) (h : 1/64 ≤ x) :
    Encloses (inv a) (1 / x) := by
  have h₀ : ((1/64 : ℚ) : ℝ) ≤ x := by simpa using h
  have hl := (encloses_clampLo hx h₀).1
  have hlpos : 0 < ((max (1/64) a.1 : ℚ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1/64) (le_max_left _ _))
  have hroundLo : ((down (1 / a.2) : ℚ) : ℝ) ≤ 1 / (a.2 : ℝ) := by
    exact_mod_cast down_le (1 / a.2)
  have hroundHi : 1 / ((max (1/64) a.1 : ℚ) : ℝ) ≤ (up (1 / max (1/64) a.1) : ℚ) := by
    exact_mod_cast le_up (1 / max (1/64) a.1)
  exact ⟨hroundLo.trans (one_div_le_one_div_of_le (hlpos.trans_le hl) hx.2),
    (one_div_le_one_div_of_le hlpos hl).trans hroundHi⟩

private def sqrtFloor (x : ℚ) : ℕ := (⌊x * grid ^ 2⌋ : ℤ).toNat.sqrt

private def root (a : Bounds) : Bounds :=
  ((sqrtFloor (max (1/8) a.1) : ℚ) / grid, ((sqrtFloor (min 8 a.2) + 1 : ℕ) : ℚ) / grid)

private theorem grid_pos : 0 < grid := by norm_num [grid]

private theorem sqrtFloor_lo {x : ℚ} (hx : 0 ≤ x) :
    ((sqrtFloor x : ℚ) / grid)^2 ≤ x := by
  rw [div_pow, div_le_iff₀ (pow_pos grid_pos _)]
  have hz : 0 ≤ ⌊x * grid^2⌋ := Int.floor_nonneg.mpr (mul_nonneg hx (sq_nonneg _))
  have hn := Nat.sqrt_le' (⌊x * grid^2⌋ : ℤ).toNat
  have hi : ((sqrtFloor x : ℤ) ^ 2) ≤ ⌊x * grid^2⌋ := by
    rw [← Int.toNat_of_nonneg hz]
    exact_mod_cast hn
  have hq : (sqrtFloor x : ℚ)^2 ≤ (⌊x * grid^2⌋ : ℤ) := by exact_mod_cast hi
  exact hq.trans (Int.floor_le _)

private theorem sqrtFloor_hi {x : ℚ} (hx : 0 ≤ x) :
    x ≤ (((sqrtFloor x + 1 : ℕ) : ℚ) / grid)^2 := by
  rw [div_pow, le_div_iff₀ (pow_pos grid_pos _)]
  have hz : 0 ≤ ⌊x * grid^2⌋ := Int.floor_nonneg.mpr (mul_nonneg hx (sq_nonneg _))
  have hn := Nat.lt_succ_sqrt' (⌊x * grid^2⌋ : ℤ).toNat
  have hi : ⌊x * grid^2⌋ + 1 ≤ ((sqrtFloor x + 1 : ℕ) : ℤ)^2 := by
    rw [← Int.toNat_of_nonneg hz]
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have hq : (⌊x * grid^2⌋ : ℤ) + (1 : ℚ) ≤ ((sqrtFloor x + 1 : ℕ) : ℚ)^2 := by
    exact_mod_cast hi
  exact (Int.lt_floor_add_one _).le.trans hq

private theorem encloses_root {a : Bounds} {x : ℝ} (hx : Encloses a x)
    (hl : 1/8 ≤ x) (hu : x ≤ 8) : Encloses (root a) (Real.sqrt x) := by
  have hl' : ((1/8 : ℚ) : ℝ) ≤ x := by simpa using hl
  have hu' : x ≤ ((8 : ℚ) : ℝ) := by exact_mod_cast hu
  have hb := encloses_clampHi (encloses_clampLo hx hl') hu'
  have hlo : 0 ≤ max (1/8) a.1 := (by norm_num : (0 : ℚ) ≤ 1/8).trans (le_max_left _ _)
  have hhi : 0 ≤ min 8 a.2 := hlo.trans (encloses_ordered hb)
  exact sqrt_box_of_square_bounds (div_nonneg (Nat.cast_nonneg _) grid_pos.le)
    (div_nonneg (Nat.cast_nonneg _) grid_pos.le) (sqrtFloor_lo hlo) (sqrtFloor_hi hhi) hb

private abbrev DyadicInterval := ℤ × ℤ

private def gridInt : ℤ := 17592186044416

private def gridValue (n : ℤ) : ℚ := (n : ℚ) / grid

private def dyadicBounds (a : DyadicInterval) : Bounds :=
  (gridValue a.1, gridValue a.2)

private def dyadicPoint (n : ℤ) : DyadicInterval := (gridInt * n, gridInt * n)

private def dyadicNeg (a : DyadicInterval) : DyadicInterval := (-a.2, -a.1)

private def dyadicAdd (a b : DyadicInterval) : DyadicInterval := (a.1 + b.1, a.2 + b.2)

private def dyadicMul (a b : DyadicInterval) : DyadicInterval :=
  let p := a.1 * b.1
  let q := a.1 * b.2
  let r := a.2 * b.1
  let s := a.2 * b.2
  (min (min p q) (min r s) / gridInt, -(-max (max p q) (max r s) / gridInt))

private theorem dyadicPoint_bounds (n : ℤ) :
    dyadicBounds (dyadicPoint n) = point (n : ℚ) := by
  have h : (gridInt : ℚ) = grid := rfl
  simp [dyadicBounds, dyadicPoint, gridValue, h, grid_pos.ne', point]

private theorem dyadicNeg_bounds (a : DyadicInterval) :
    dyadicBounds (dyadicNeg a) = neg (dyadicBounds a) := by
  simp [dyadicBounds, dyadicNeg, neg, gridValue, neg_div]

private theorem dyadicAdd_bounds (a b : DyadicInterval) :
    dyadicBounds (dyadicAdd a b) = add (dyadicBounds a) (dyadicBounds b) := by
  simp [dyadicBounds, dyadicAdd, add, gridValue, add_div]

private theorem gridValue_mul (m n : ℤ) :
    gridValue m * gridValue n = ((m * n : ℤ) : ℚ) / grid ^ 2 := by
  simp only [gridValue, Int.cast_mul, div_mul_div_comm, pow_two]

private theorem down_gridProduct (n : ℤ) :
    down ((n : ℚ) / grid ^ 2) = gridValue (n / gridInt) := by
  have hcancel : (n : ℚ) / grid ^ 2 * grid = (n : ℚ) / grid := by
    field_simp [grid_pos.ne']
  rw [down, hcancel]
  change (⌊(n : ℚ) / ((17592186044416 : ℕ) : ℚ)⌋ : ℚ) / grid = _
  rw [Rat.floor_intCast_div_natCast]
  rfl

private theorem up_gridProduct (n : ℤ) :
    up ((n : ℚ) / grid ^ 2) = gridValue (-(-n / gridInt)) := by
  rw [up, ← neg_div, ← Int.cast_neg, down_gridProduct]
  simp [gridValue, neg_div]

private theorem dyadicMul_bounds (a b : DyadicInterval) :
    dyadicBounds (dyadicMul a b) = mul (dyadicBounds a) (dyadicBounds b) := by
  simp only [dyadicBounds, dyadicMul, mul, gridValue_mul,
    min_div_div_right (sq_nonneg grid), max_div_div_right (sq_nonneg grid),
    ← Int.cast_min, ← Int.cast_max, down_gridProduct, up_gridProduct]

private theorem dyadicPoint_encloses (n : ℤ) :
    Encloses (dyadicBounds (dyadicPoint n)) (n : ℝ) := by
  rw [dyadicPoint_bounds]
  simpa only [Rat.cast_intCast] using encloses_point (n : ℚ)

private theorem dyadicAdd_encloses {a b : DyadicInterval} {x y : ℝ}
    (hx : Encloses (dyadicBounds a) x) (hy : Encloses (dyadicBounds b) y) :
    Encloses (dyadicBounds (dyadicAdd a b)) (x + y) := by
  rw [dyadicAdd_bounds]
  exact encloses_add hx hy

private theorem dyadicMul_encloses {a b : DyadicInterval} {x y : ℝ}
    (hx : Encloses (dyadicBounds a) x) (hy : Encloses (dyadicBounds b) y) :
    Encloses (dyadicBounds (dyadicMul a b)) (x * y) := by
  rw [dyadicMul_bounds]
  exact encloses_mul hx hy

private def dyadicFraction (n : ℤ) (d : ℕ) : DyadicInterval :=
  (n * gridInt / (d : ℤ), -((-n) * gridInt / (d : ℤ)))

private theorem dyadicFraction_bounds (n : ℤ) (d : ℕ) :
    dyadicBounds (dyadicFraction n d) =
      (down ((n : ℚ) / (d : ℚ)), up ((n : ℚ) / (d : ℚ))) := by
  have hf (m : ℤ) : ⌊((m : ℚ) / (d : ℚ)) * grid⌋ = m * gridInt / (d : ℤ) := by
    rw [div_mul_eq_mul_div, ← show (gridInt : ℚ) = grid by rfl, ← Int.cast_mul,
      Rat.floor_intCast_div_natCast]
  simp only [dyadicBounds, dyadicFraction, down, up, hf, gridValue,
    ← neg_div, ← Int.cast_neg]

private theorem dyadicFraction_encloses (n : ℤ) (d : ℕ) :
    Encloses (dyadicBounds (dyadicFraction n d)) ((n : ℝ) / (d : ℝ)) := by
  rw [dyadicFraction_bounds]
  simpa only [Encloses, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    And.intro (Rat.cast_le (K := ℝ).mpr (down_le ((n : ℚ) / (d : ℚ))))
      (Rat.cast_le (K := ℝ).mpr (le_up ((n : ℚ) / (d : ℚ))))

private def dyadicHorner (h : DyadicInterval) (denom : ℕ) : List ℤ → DyadicInterval
  | [] => dyadicPoint 0
  | c :: cs => dyadicAdd (dyadicMul (dyadicHorner h denom cs) h) (dyadicFraction c denom)

private theorem dyadicHorner_encloses {hbox : DyadicInterval} {h : ℝ}
    (hh : Encloses (dyadicBounds hbox) h) (denom : ℕ) (cs : List ℤ) :
    Encloses (dyadicBounds (dyadicHorner hbox denom cs))
      (momentHorner h (cs.map fun (c : ℤ) ↦ (c : ℚ) / (denom : ℚ))) := by
  induction cs with
  | nil => simpa [dyadicHorner, momentHorner] using dyadicPoint_encloses 0
  | cons c cs ih =>
    simpa only [List.map_cons, dyadicHorner, momentHorner, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_natCast, mul_comm, add_comm] using
      dyadicAdd_encloses (dyadicMul_encloses ih hh) (dyadicFraction_encloses c denom)

/-- The dyadic enclosure operations shared by the compact kernel certificates. -/
structure RoundedInterval where
  endpoints : ℤ × ℤ

namespace RoundedInterval

def lower (I : RoundedInterval) : ℚ := (dyadicBounds I.endpoints).1
def upper (I : RoundedInterval) : ℚ := (dyadicBounds I.endpoints).2
def encloses (I : RoundedInterval) (x : ℝ) : Prop := Encloses (dyadicBounds I.endpoints) x

def interval (lo hi : ℚ) : RoundedInterval :=
  ⟨(dyadicFraction lo.num lo.den).1, (dyadicFraction hi.num hi.den).2⟩

def point (q : ℚ) : RoundedInterval := interval q q

instance : Add RoundedInterval := ⟨fun a b ↦ ⟨dyadicAdd a.endpoints b.endpoints⟩⟩
instance : Sub RoundedInterval := ⟨fun a b ↦ ⟨dyadicAdd a.endpoints (dyadicNeg b.endpoints)⟩⟩
instance : Mul RoundedInterval := ⟨fun a b ↦ ⟨dyadicMul a.endpoints b.endpoints⟩⟩
instance : Zero RoundedInterval := ⟨point 0⟩

theorem encloses_interval {lo hi : ℚ} {x : ℝ} (hl : (lo : ℝ) ≤ x) (hu : x ≤ (hi : ℝ)) :
    (interval lo hi).encloses x := by
  have hc (q : ℚ) : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact_mod_cast q.num_div_den
  have hL := dyadicFraction_encloses lo.num lo.den
  have hU := dyadicFraction_encloses hi.num hi.den
  rw [hc] at hL hU
  exact ⟨hL.1.trans hl, hu.trans hU.2⟩

theorem encloses_point (q : ℚ) : (point q).encloses (q : ℝ) :=
  encloses_interval le_rfl le_rfl

theorem encloses_add {a b : RoundedInterval} {x y : ℝ} (ha : a.encloses x) (hb : b.encloses y) :
    (a + b).encloses (x + y) := dyadicAdd_encloses ha hb

theorem encloses_sub {a b : RoundedInterval} {x y : ℝ} (ha : a.encloses x) (hb : b.encloses y) :
    (a - b).encloses (x - y) := by
  rw [sub_eq_add_neg]
  refine dyadicAdd_encloses ha ?_
  rw [dyadicNeg_bounds]
  exact encloses_neg hb

theorem encloses_mul {a b : RoundedInterval} {x y : ℝ} (ha : a.encloses x) (hb : b.encloses y) :
    (a * b).encloses (x * y) := dyadicMul_encloses ha hb

end RoundedInterval

end RefinedBMV.PositiveCenter.SmallCorner
