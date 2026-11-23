/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CornerEnclosures
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational interval bounds and analytic soundness for the small-corner cover. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MixedJet
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MarginalTaylor
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentTable
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.JointTaylorReplay
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.WeightedTaylorReplay
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Box

/-! Rational enclosures for the regularized positive-center expression. -/

namespace RefinedBMV.PositiveCenter.SmallCorner

open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open RefinedBMV.FourSpectrumLift (sqrt_box_of_square_bounds)

set_option autoImplicit false

private abbrev Bounds := ℚ × ℚ

def Encloses (a : Bounds) (x : ℝ) : Prop :=
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

private def scalar (x : Bounds) : MixedJet Bounds := ⟨x, point 0, point 0, point 0⟩

private local instance : Add Bounds := ⟨add⟩
private local instance : Sub Bounds := ⟨sub⟩
private local instance : Neg Bounds := ⟨neg⟩
private local instance : Mul Bounds := ⟨mul⟩

def JetEncloses (a : MixedJet Bounds) (x : MixedJet ℝ) : Prop :=
  Encloses a.value x.value ∧ Encloses a.du x.du ∧ Encloses a.dv x.dv ∧ Encloses a.duv x.duv

private theorem jet_scalar {a : Bounds} {x : ℝ} (hx : Encloses a x) :
    JetEncloses (scalar a) ⟨x, 0, 0, 0⟩ := by
  have hz : Encloses (point 0) 0 := by norm_num [Encloses, point]
  exact ⟨hx, hz, hz, hz⟩

private theorem jet_add {a b : MixedJet Bounds} {x y : MixedJet ℝ}
    (hx : JetEncloses a x) (hy : JetEncloses b y) :
    JetEncloses (a.add b) (x.add y) :=
  ⟨encloses_add hx.1 hy.1, encloses_add hx.2.1 hy.2.1,
    encloses_add hx.2.2.1 hy.2.2.1, encloses_add hx.2.2.2 hy.2.2.2⟩

private theorem jet_sub {a b : MixedJet Bounds} {x y : MixedJet ℝ}
    (hx : JetEncloses a x) (hy : JetEncloses b y) :
    JetEncloses (a.sub b) (x.sub y) :=
  ⟨encloses_sub hx.1 hy.1, encloses_sub hx.2.1 hy.2.1,
    encloses_sub hx.2.2.1 hy.2.2.1, encloses_sub hx.2.2.2 hy.2.2.2⟩

private theorem jet_mul {a b : MixedJet Bounds} {x y : MixedJet ℝ}
    (hx : JetEncloses a x) (hy : JetEncloses b y) :
    JetEncloses (a.mul b) (x.mul y) :=
  ⟨encloses_mul hx.1 hy.1,
    encloses_add (encloses_mul hx.2.1 hy.1) (encloses_mul hx.1 hy.2.1),
    encloses_add (encloses_mul hx.2.2.1 hy.1) (encloses_mul hx.1 hy.2.2.1),
    encloses_add (encloses_add (encloses_add (encloses_mul hx.2.2.2 hy.1)
      (encloses_mul hx.2.1 hy.2.2.1)) (encloses_mul hx.2.2.1 hy.2.1))
      (encloses_mul hx.1 hy.2.2.2)⟩

private def jetInv (a : MixedJet Bounds) : MixedJet Bounds :=
  let q := inv a.value
  let q₂ := q * q
  ⟨q, -(q₂ * a.du), -(q₂ * a.dv), q₂ * (point 2 * q * a.du * a.dv - a.duv)⟩

private theorem jet_inv {a : MixedJet Bounds} {x : MixedJet ℝ}
    (hx : JetEncloses a x) (h : 1/64 ≤ x.value) :
    JetEncloses (jetInv a) x.reciprocal := by
  have hq := encloses_inv hx.1 h
  have hq₂ := encloses_mul hq hq
  have htwo : Encloses (point 2) 2 := by exact ⟨by norm_num [point], by norm_num [point]⟩
  exact ⟨hq, encloses_neg (encloses_mul hq₂ hx.2.1),
    encloses_neg (encloses_mul hq₂ hx.2.2.1),
    encloses_mul hq₂ (encloses_sub
      (encloses_mul (encloses_mul (encloses_mul htwo hq) hx.2.1) hx.2.2.1) hx.2.2.2)⟩

private def jetRoot (a : MixedJet Bounds) : MixedJet Bounds :=
  let r := root a.value
  let q := inv (point 2 * r)
  ⟨r, q * a.du, q * a.dv, q * a.duv - q * q * inv r * a.du * a.dv⟩

private theorem quarter_le_sqrt {x : ℝ} (h : 1/8 ≤ x) : 1/4 ≤ √x := by
  exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)

private theorem jet_root {a : MixedJet Bounds} {x : MixedJet ℝ}
    (hx : JetEncloses a x) (hl : 1/8 ≤ x.value) (hu : x.value ≤ 8) :
    JetEncloses (jetRoot a) (x.sqrtFrom (Real.sqrt x.value)) := by
  have hr := encloses_root hx.1 hl hu
  have hr₀ := quarter_le_sqrt hl
  have htwo : Encloses (point 2) 2 := by exact ⟨by norm_num [point], by norm_num [point]⟩
  have hq := encloses_inv (encloses_mul htwo hr) (by linarith)
  have hi := encloses_inv hr (by linarith)
  exact ⟨hr, encloses_mul hq hx.2.1, encloses_mul hq hx.2.2.1,
    encloses_sub (encloses_mul hq hx.2.2.2)
      (encloses_mul (encloses_mul (encloses_mul (encloses_mul hq hq) hi) hx.2.1) hx.2.2.1)⟩

structure CornerInputs (R : Type) where
  joint : MixedJet R
  prime : MixedJet R
  firstDifference : MixedJet R
  secondDifference : MixedJet R
  atV : MixedJet R
  atD : MixedJet R
  atNegU : MixedJet R
  atNegV : MixedJet R

private def regularizedJet {R : Type} [Add R] [Sub R] [Mul R]
    (squareRoot reciprocal : MixedJet R → MixedJet R) (half v d : MixedJet R)
    (x : CornerInputs R) : MixedJet R :=
  let slope := x.firstDifference.mul (reciprocal ((squareRoot x.atV).add (squareRoot x.atD)))
  let n := (x.joint.sub ((half.mul v).mul x.prime)).add
    (((half.mul v).mul d).mul ((slope.mul slope).sub x.secondDifference))
  n.mul (reciprocal ((squareRoot x.atNegU).mul (squareRoot x.atNegV)))

private def cornerFormula {R : Type} [Add R] [Sub R] [Neg R] [Mul R]
    (squareRoot reciprocal : MixedJet R → MixedJet R) (half u v d : MixedJet R)
    (x : CornerInputs R) : R :=
  let f := regularizedJet squareRoot reciprocal half v d x
  (-f.value - u.value * f.du) + v.value * f.dv + u.value * v.value * f.duv

private def cornerBounds (u d : Bounds) (x : CornerInputs Bounds) : Bounds :=
  cornerFormula jetRoot jetInv (scalar (point (1/2)))
    ⟨u, point 1, point 0, point 0⟩ ⟨u+d, point 0, point 1, point 0⟩
    ⟨d, point (-1), point 1, point 0⟩ x

def Radicand (x : MixedJet ℝ) : Prop :=
  1/8 ≤ x.value ∧ x.value ≤ 8

def CornerEncloses (a : CornerInputs Bounds) (x : CornerInputs ℝ) : Prop :=
  JetEncloses a.joint x.joint ∧ JetEncloses a.prime x.prime ∧
  JetEncloses a.firstDifference x.firstDifference ∧ JetEncloses a.secondDifference x.secondDifference ∧
  JetEncloses a.atV x.atV ∧ JetEncloses a.atD x.atD ∧
  JetEncloses a.atNegU x.atNegU ∧ JetEncloses a.atNegV x.atNegV

noncomputable def realCorner (u d : ℝ) (x : CornerInputs ℝ) : ℝ :=
  cornerFormula (fun a ↦ a.sqrtFrom (Real.sqrt a.value)) MixedJet.reciprocal
    ⟨1/2, 0, 0, 0⟩ ⟨u, 1, 0, 0⟩ ⟨u+d, 0, 1, 0⟩ ⟨d, -1, 1, 0⟩ x

private theorem corner_encloses {ub db : Bounds} {u d : ℝ}
    {a : CornerInputs Bounds} {x : CornerInputs ℝ} (hu : Encloses ub u) (hd : Encloses db d)
    (hx : CornerEncloses a x) (hV : Radicand x.atV) (hD : Radicand x.atD)
    (hNegU : Radicand x.atNegU) (hNegV : Radicand x.atNegV) :
    Encloses (cornerBounds ub db a) (realCorner u d x) := by
  have hzero : Encloses (point 0) 0 := ⟨by norm_num [point], by norm_num [point]⟩
  have hone : Encloses (point 1) 1 := ⟨by norm_num [point], by norm_num [point]⟩
  have hnegone : Encloses (point (-1)) (-1) := ⟨by norm_num [point], by norm_num [point]⟩
  have hhalf : JetEncloses (scalar (point (1/2))) ⟨1/2, 0, 0, 0⟩ :=
    jet_scalar (by exact ⟨by norm_num [point], by norm_num [point]⟩)
  have hv := encloses_add hu hd
  have hvj : JetEncloses ⟨ub+db, point 0, point 1, point 0⟩ ⟨u+d, 0, 1, 0⟩ :=
    ⟨hv, hzero, hone, hzero⟩
  have hdj : JetEncloses ⟨db, point (-1), point 1, point 0⟩ ⟨d, -1, 1, 0⟩ :=
    ⟨hd, hnegone, hone, hzero⟩
  rcases hx with ⟨hj, hp, hfirst, hsecond, hv₀, hd₀, hnu, hnv⟩
  have hsum := jet_add (jet_root hv₀ hV.1 hV.2) (jet_root hd₀ hD.1 hD.2)
  have hsumPos : 1/64 ≤ √x.atV.value + √x.atD.value := by
    linarith [quarter_le_sqrt hV.1, quarter_le_sqrt hD.1]
  have hs := jet_mul hfirst (jet_inv hsum hsumPos)
  have hh := jet_mul hhalf hvj
  have hn := jet_add (jet_sub hj (jet_mul hh hp))
    (jet_mul (jet_mul hh hdj) (jet_sub (jet_mul hs hs) hsecond))
  have hprod := jet_mul (jet_root hnu hNegU.1 hNegU.2) (jet_root hnv hNegV.1 hNegV.2)
  have hprodPos : 1/64 ≤ √x.atNegU.value * √x.atNegV.value := by
    have h := mul_le_mul (quarter_le_sqrt hNegU.1) (quarter_le_sqrt hNegV.1)
      (by norm_num) (Real.sqrt_nonneg x.atNegU.value)
    linarith
  have hf := jet_mul hn (jet_inv hprod hprodPos)
  exact encloses_add (encloses_add
    (encloses_sub (encloses_neg hf.1) (encloses_mul hu hf.2.1))
    (encloses_mul hv hf.2.2.1)) (encloses_mul (encloses_mul hu hv) hf.2.2.2)

/-- The six closed leaves use the independent coordinates `u,d,h`. -/
def sixBox (i : Fin 6) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) :=
  ![
    ((0, (1 / 4)), (0, (1 / 2)), (0, (35 / 128))),
    (((1 / 4), (1 / 2)), (0, (1 / 4)), (0, (35 / 128))),
    (((1 / 4), (3 / 8)), ((1 / 4), (1 / 2)), (0, (35 / 128))),
    (((3 / 8), (1 / 2)), ((1 / 4), (3 / 8)), (0, (35 / 128))),
    (((3 / 8), (1 / 2)), ((3 / 8), (1 / 2)), (0, (35 / 256))),
    (((3 / 8), (1 / 2)), ((3 / 8), (1 / 2)), ((35 / 256), (35 / 128)))
  ] i

/-- The degree-12 exact-coefficient replay, with outward rounding and Taylor error. -/
def primitiveBounds (i : Fin 6) : CornerInputs Bounds :=
  ![
    ⟨⟨(14277840483204 / 17592186044416, 20083414888713 / 17592186044416), (-1258961557581 / 17592186044416, 3887771528750 / 17592186044416), (-5539237112965 / 17592186044416, 9243720297339 / 17592186044416), (-6537082958086 / 17592186044416, -2509529470537 / 17592186044416)⟩,
     ⟨(2345624789538 / 17592186044416, 7199048892915 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (3518437192498 / 17592186044416, 8216488108100 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(2345624789538 / 17592186044416, 6247334712548 / 17592186044416), (-3528776817287 / 17592186044416, -1759218588057 / 17592186044416), (3518437192498 / 17592186044416, 7335633538757 / 17592186044416), (-3161954696908 / 17592186044416, -1005267757580 / 17592186044416)⟩,
     ⟨(1759218588057 / 17592186044416, 3806856737856 / 17592186044416), (-1112319698667 / 17592186044416, -335089241604 / 17592186044416), (1005267757580 / 17592186044416, 3523418293784 / 17592186044416), (-1445854403891 / 17592186044416, -432823608516 / 17592186044416)⟩,
     ⟨(17592186028032 / 17592186044416, 21119151252931 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (2345624789538 / 17592186044416, 7199048892915 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(17592186028032 / 17592186044416, 19557317578890 / 17592186044416), (-5365140512323 / 17592186044416, -2345624789538 / 17592186044416), (2345624789538 / 17592186044416, 5365140512323 / 17592186044416), (-6545144868628 / 17592186044416, -3518437192498 / 17592186044416)⟩,
     ⟨(16925607103692 / 17592186044416, 17592186060800 / 17592186044416), (-2666315713742 / 17592186044416, -1225497318740 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(15592449255013 / 17592186044416, 17592186060800 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-2666315713742 / 17592186044416, 1014757622856 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩⟩,
    ⟨⟨(15091627826747 / 17592186044416, 20808294454174 / 17592186044416), (-798920917964 / 17592186044416, 4467442096068 / 17592186044416), (-4494539771226 / 17592186044416, 8531892687040 / 17592186044416), (-7307873942449 / 17592186044416, -2554375904718 / 17592186044416)⟩,
     ⟨(3295263246639 / 17592186044416, 7199048892915 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (4109336263033 / 17592186044416, 8216488108100 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(2808149678016 / 17592186044416, 5424358567520 / 17592186044416), (-3073236316087 / 17592186044416, -1850099537323 / 17592186044416), (3798553810254 / 17592186044416, 6622616966886 / 17592186044416), (-2564514170711 / 17592186044416, -1120466445193 / 17592186044416)⟩,
     ⟨(1948454256161 / 17592186044416, 3549380667186 / 17592186044416), (-952288718591 / 17592186044416, -393418848533 / 17592186044416), (1243129708233 / 17592186044416, 3187742298896 / 17592186044416), (-1246456272840 / 17592186044416, -490652598971 / 17592186044416)⟩,
     ⟨(18294223451641 / 17592186044416, 21119151252931 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (3295263246639 / 17592186044416, 7199048892915 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(17592186028032 / 17592186044416, 18406971977364 / 17592186044416), (-3887740417670 / 17592186044416, -2345624789538 / 17592186044416), (2345624789538 / 17592186044416, 3887740417670 / 17592186044416), (-5340359889728 / 17592186044416, -3518437192498 / 17592186044416)⟩,
     ⟨(16450412154586 / 17592186044416, 17277960257745 / 17592186044416), (-1955562346933 / 17592186044416, -189297518861 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(15857813454423 / 17592186044416, 17416035026804 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-2042142948507 / 17592186044416, 920632754141 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩⟩,
    ⟨⟨(15863612652161 / 17592186044416, 21325902356382 / 17592186044416), (-1599405770986 / 17592186044416, 2854084297926 / 17592186044416), (-750288704371 / 17592186044416, 11697566503554 / 17592186044416), (-7408627905579 / 17592186044416, -2738086374717 / 17592186044416)⟩,
     ⟨(4417753988028 / 17592186044416, 8290720447232 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (4910346531002 / 17592186044416, 9278975077916 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(3839842981010 / 17592186044416, 6742830480117 / 17592186044416), (-3673839930504 / 17592186044416, -2178318857282 / 17592186044416), (4489962681725 / 17592186044416, 7801546509476 / 17592186044416), (-3350404391998 / 17592186044416, -1522504208961 / 17592186044416)⟩,
     ⟨(2311643808058 / 17592186044416, 4127706595359 / 17592186044416), (-1210311122684 / 17592186044416, -533298794847 / 17592186044416), (1681530091734 / 17592186044416, 3939809532269 / 17592186044416), (-1571747057273 / 17592186044416, -636084546291 / 17592186044416)⟩,
     ⟨(19254184202922 / 17592186044416, 22085879002790 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (4417753988028 / 17592186044416, 8290720447232 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(18294223451654 / 17592186044416, 19557317578890 / 17592186044416), (-5365140512323 / 17592186044416, -3295263247236 / 17592186044416), (3295263247236 / 17592186044416, 5365140512323 / 17592186044416), (-6545144868628 / 17592186044416, -4109336292738 / 17592186044416)⟩,
     ⟨(16741243010415 / 17592186044416, 17209421463897 / 17592186044416), (-1912813541214 / 17592186044416, -736262148168 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(15860242349241 / 17592186044416, 17357797758841 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-1474963238660 / 17592186044416, 1386820934122 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩⟩,
    ⟨⟨(16386593096184 / 17592186044416, 21490608146778 / 17592186044416), (-1361363920798 / 17592186044416, 3107407910250 / 17592186044416), (111411955781 / 17592186044416, 11277313249842 / 17592186044416), (-7758628383671 / 17592186044416, -2669357941835 / 17592186044416)⟩,
     ⟨(5061947296194 / 17592186044416, 8290720447232 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (5408902077070 / 17592186044416, 9278975077916 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(4138115070396 / 17592186044416, 6299676587568 / 17592186044416), (-3421615179673 / 17592186044416, -2247604814846 / 17592186044416), (4711157115151 / 17592186044416, 7403702899032 / 17592186044416), (-3021312522899 / 17592186044416, -1604854455689 / 17592186044416)⟩,
     ⟨(2463552276580 / 17592186044416, 3982087735746 / 17592186044416), (-1120945128547 / 17592186044416, -575859418860 / 17592186044416), (1860647539390 / 17592186044416, 3750544374428 / 17592186044416), (-1458463719744 / 17592186044416, -682102716802 / 17592186044416)⟩,
     ⟨(19846016614236 / 17592186044416, 22085879002790 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (5061947296194 / 17592186044416, 8290720447232 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(18294223451658 / 17592186044416, 18936040717200 / 17592186044416), (-4588869005924 / 17592186044416, -3295263247416 / 17592186044416), (3295263247416 / 17592186044416, 4588869005924 / 17592186044416), (-5893046645785 / 17592186044416, -4109336300273 / 17592186044416)⟩,
     ⟨(16547166874509 / 17592186044416, 17114885581843 / 17592186044416), (-1592073410849 / 17592186044416, -232188402464 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(16015211705448 / 17592186044416, 17285665509987 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-1157563117678 / 17592186044416, 1336186408358 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩⟩,
    ⟨⟨(17191470948865 / 17592186044416, 21824055333965 / 17592186044416), (-1403671513404 / 17592186044416, 2036431827092 / 17592186044416), (2570478763572 / 17592186044416, 12273462024598 / 17592186044416), (-7193263499105 / 17592186044416, -3002482520029 / 17592186044416)⟩,
     ⟨(5773240497093 / 17592186044416, 8470557965196 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (5985736235966 / 17592186044416, 8936316532284 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(4755467399614 / 17592186044416, 6546791334956 / 17592186044416), (-3314551222527 / 17592186044416, -2463863300675 / 17592186044416), (5177924846883 / 17592186044416, 7162084483109 / 17592186044416), (-2888147846517 / 17592186044416, -1861036171152 / 17592186044416)⟩,
     ⟨(2714061529823 / 17592186044416, 3847533276966 / 17592186044416), (-1065964125394 / 17592186044416, -667190390626 / 17592186044416), (2154157938656 / 17592186044416, 3548464116246 / 17592186044416), (-1320632557659 / 17592186044416, -781613716503 / 17592186044416)⟩,
     ⟨(20522465071214 / 17592186044416, 22678861981258 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (5773240497093 / 17592186044416, 8470557965196 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(18739164790213 / 17592186044416, 19405466321977 / 17592186044416), (-4889515731891 / 17592186044416, -3831518460019 / 17592186044416), (3831518460019 / 17592186044416, 4889515731891 / 17592186044416), (-5718010568114 / 17592186044416, -4480034216634 / 17592186044416)⟩,
     ⟨(16634377538501 / 17592186044416, 17068615305503 / 17592186044416), (-1388872980721 / 17592186044416, -485305637173 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(16147793505622 / 17592186044416, 17216174219474 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-608177350434 / 17592186044416, 1278324905728 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩⟩,
    ⟨⟨(17295317899722 / 17592186044416, 22522911795515 / 17592186044416), (-1734141264584 / 17592186044416, 2073886457810 / 17592186044416), (3298727218611 / 17592186044416, 14409141742805 / 17592186044416), (-8274615384831 / 17592186044416, -3519784612500 / 17592186044416)⟩,
     ⟨(6463118737944 / 17592186044416, 9500622928411 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (7054424754639 / 17592186044416, 10494996957070 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(5272919262506 / 17592186044416, 7262634004473 / 17592186044416), (-3818117778301 / 17592186044416, -2858801143507 / 17592186044416), (6032666199942 / 17592186044416, 8294095626292 / 17592186044416), (-3547920755881 / 17592186044416, -2333566416043 / 17592186044416)⟩,
     ⟨(3173864687021 / 17592186044416, 4475977864375 / 17592186044416), (-1315720188660 / 17592186044416, -840168962259 / 17592186044416), (2724682221747 / 17592186044416, 4401802679520 / 17592186044416), (-1707763865435 / 17592186044416, -1042952973519 / 17592186044416)⟩,
     ⟨(20813280491673 / 17592186044416, 23185806601626 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (6463118737944 / 17592186044416, 9500622928411 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(18835935762089 / 17592186044416, 19554489607587 / 17592186044416), (-5353575123521 / 17592186044416, -4200868827545 / 17592186044416), (4200868827545 / 17592186044416, 5353575123521 / 17592186044416), (-6520135256613 / 17592186044416, -5157577909998 / 17592186044416)⟩,
     ⟨(16591334946529 / 17592186044416, 17047655287519 / 17592186044416), (-1410918746757 / 17592186044416, -444453479201 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩,
     ⟨(16117814577311 / 17592186044416, 17244590696435 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416), (-540363754019 / 17592186044416, 1502351625699 / 17592186044416), (-16384 / 17592186044416, 16384 / 17592186044416)⟩⟩
  ] i

theorem six_box_cover {u d h : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1/2) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1/2)
    (hh₀ : 0 ≤ h) (hh₁ : h ≤ 35/128) :
    ∃ i : Fin 6, Encloses (sixBox i).1 u ∧ Encloses (sixBox i).2.1 d ∧
      Encloses (sixBox i).2.2 h := by
  by_cases hU : u ≤ 1/4
  · exact ⟨0, by norm_num [sixBox, Encloses]; exact ⟨⟨hu₀, hU⟩, ⟨hd₀, hd₁⟩, hh₀, hh₁⟩⟩
  by_cases hD : d ≤ 1/4
  · exact ⟨1, by norm_num [sixBox, Encloses]; exact ⟨⟨le_of_not_ge hU, hu₁⟩, ⟨hd₀, hD⟩, hh₀, hh₁⟩⟩
  by_cases hU' : u ≤ 3/8
  · exact ⟨2, by norm_num [sixBox, Encloses]; exact ⟨⟨le_of_not_ge hU, hU'⟩, ⟨le_of_not_ge hD, hd₁⟩, hh₀, hh₁⟩⟩
  by_cases hD' : d ≤ 3/8
  · exact ⟨3, by norm_num [sixBox, Encloses]; exact ⟨⟨le_of_not_ge hU', hu₁⟩, ⟨le_of_not_ge hD, hD'⟩, hh₀, hh₁⟩⟩
  by_cases hH : h ≤ 35/256
  · exact ⟨4, by norm_num [sixBox, Encloses]; exact ⟨⟨le_of_not_ge hU', hu₁⟩, ⟨le_of_not_ge hD', hd₁⟩, hh₀, hH⟩⟩
  exact ⟨5, by norm_num [sixBox, Encloses]; exact ⟨⟨le_of_not_ge hU', hu₁⟩, ⟨le_of_not_ge hD', hd₁⟩, le_of_not_ge hH, hh₁⟩⟩

private def scaledUpper (i : Fin 6) : ℤ :=
  ![-1969588407261, -5060001568589, -2137902120202,
    -4559245335572, -4692821502326, -2551082877845] i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem box_upper_check (i : Fin 6) :
    (cornerBounds (sixBox i).1 (sixBox i).2.1 (primitiveBounds i)).2 ≤
      (scaledUpper i : ℚ) / grid := by
  fin_cases i <;> decide +kernel

#print axioms box_upper_check

private theorem box_uniform_upper (i : Fin 6) :
    (scaledUpper i : ℚ) / grid ≤ (-1969588407261 : ℚ) / 17592186044416 := by
  fin_cases i <;> decide +kernel

/-- Conditional on the eight primitive jet enclosures, interval arithmetic bounds
the real regularized expression on every one of the six closed leaves. -/
theorem six_box_regularized_upper (i : Fin 6) {u d : ℝ} {x : CornerInputs ℝ}
    (hu : Encloses (sixBox i).1 u) (hd : Encloses (sixBox i).2.1 d)
    (hx : CornerEncloses (primitiveBounds i) x) (hv : Radicand x.atV)
    (hd₀ : Radicand x.atD) (hnu : Radicand x.atNegU) (hnv : Radicand x.atNegV) :
    realCorner u d x ≤ (-1969588407261 : ℝ) / 17592186044416 := by
  have hb := (corner_encloses hu hd hx hv hd₀ hnu hnv).2
  have hq := (box_upper_check i).trans (box_uniform_upper i)
  exact hb.trans (by exact_mod_cast hq)

theorem six_box_regularized_lt (i : Fin 6) {u d : ℝ} {x : CornerInputs ℝ}
    (hu : Encloses (sixBox i).1 u) (hd : Encloses (sixBox i).2.1 d)
    (hx : CornerEncloses (primitiveBounds i) x) (hv : Radicand x.atV)
    (hd₀ : Radicand x.atD) (hnu : Radicand x.atNegU) (hnv : Radicand x.atNegV) :
    realCorner u d x < -1/9 :=
  (six_box_regularized_upper i hu hd hx hv hd₀ hnu hnv).trans_lt (by norm_num)

#print axioms six_box_cover
#print axioms six_box_regularized_lt

open Filter Set
open scoped Topology

/-- The regularized jet as a function of the two independent coordinates. -/
noncomputable def realRegularizedJet (x : ℝ → ℝ → CornerInputs ℝ) (u v : ℝ) : MixedJet ℝ :=
  regularizedJet (fun a ↦ a.sqrtFrom (Real.sqrt a.value)) MixedJet.reciprocal
    ⟨1/2, 0, 0, 0⟩ ⟨v, 0, 1, 0⟩ ⟨v-u, -1, 1, 0⟩ (x u v)

def PrimitiveJetsAt (x : ℝ → ℝ → CornerInputs ℝ) (u v : ℝ) : Prop :=
  MixedJet.IsAt (fun s t ↦ (x s t).joint) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).prime) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).firstDifference) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).secondDifference) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).atV) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).atD) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).atNegU) u v ∧
  MixedJet.IsAt (fun s t ↦ (x s t).atNegV) u v

theorem realRegularizedJet_isAt {x : ℝ → ℝ → CornerInputs ℝ} {u v : ℝ}
    (hx : PrimitiveJetsAt x u v) (hV : Radicand (x u v).atV) (hD : Radicand (x u v).atD)
    (hNegU : Radicand (x u v).atNegU) (hNegV : Radicand (x u v).atNegV) :
    MixedJet.IsAt (realRegularizedJet x) u v := by
  have hhalf : MixedJet.IsAt (fun _ _ ↦ ⟨1/2, 0, 0, 0⟩) u v :=
    ⟨Eventually.of_forall (fun _ ↦ hasDerivAt_const u _), hasDerivAt_const v _, hasDerivAt_const v _⟩
  have hv : MixedJet.IsAt (fun _ t ↦ ⟨t, 0, 1, 0⟩) u v :=
    ⟨Eventually.of_forall (fun _ ↦ hasDerivAt_const u _), hasDerivAt_id v, hasDerivAt_const v _⟩
  have hd : MixedJet.IsAt (fun s t ↦ ⟨t-s, -1, 1, 0⟩) u v :=
    ⟨Eventually.of_forall (fun t ↦ (hasDerivAt_id' u).const_sub t),
      (hasDerivAt_id v).sub_const u, hasDerivAt_const v _⟩
  rcases hx with ⟨hj, hp, hf, hs, hv₀, hd₀, hnu, hnv⟩
  have hRs := (hv₀.sqrtFrom (by linarith [hV.1])).add (hd₀.sqrtFrom (by linarith [hD.1]))
  have hRs₀ : √(x u v).atV.value + √(x u v).atD.value ≠ 0 := by
    linarith [quarter_le_sqrt hV.1, quarter_le_sqrt hD.1]
  have hSlope := hf.mul (hRs.reciprocal hRs₀)
  have hRprod := (hnu.sqrtFrom (by linarith [hNegU.1])).mul (hnv.sqrtFrom (by linarith [hNegV.1]))
  have hRprod₀ : √(x u v).atNegU.value * √(x u v).atNegV.value ≠ 0 :=
    mul_ne_zero (by linarith [quarter_le_sqrt hNegU.1]) (by linarith [quarter_le_sqrt hNegV.1])
  have hh := hhalf.mul hv
  exact ((hj.sub (hh.mul hp)).add ((hh.mul hd).mul ((hSlope.mul hSlope).sub hs))).mul
    (hRprod.reciprocal hRprod₀)

theorem regularized_corner_eq_mixed {p : ℕ} (hp : 0 < p) {x : ℝ → ℝ → CornerInputs ℝ}
    {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hx : PrimitiveJetsAt x u v) (hV : Radicand (x u v).atV) (hD : Radicand (x u v).atD)
    (hNegU : Radicand (x u v).atNegU) (hNegV : Radicand (x u v).atNegV)
    (heq : ∀ s t : ℝ, 0 < s → s < t →
      (realRegularizedJet x s t).value = F p (compositionMarginalVariance p / 2) s t) :
    realCorner u (v-u) (x u v) =
      v ^ 2 * deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v := by
  let f := F p (compositionMarginalVariance p / 2)
  have hj := realRegularizedJet_isAt hx hV hD hNegU hNegV
  have hfst : ∀ᶠ t in 𝓝 v, HasDerivAt (fun s ↦ f s t) (realRegularizedJet x u t).du u := by
    filter_upwards [hj.1, Ioi_mem_nhds huv] with t ht hut
    apply ht.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hu hut] with s hs
    exact (heq _ _ hs.1 hs.2).symm
  have hsnd : HasDerivAt (f u) (realRegularizedJet x u v).dv v := by
    apply hj.2.1.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds huv] with t ht
    exact (heq _ _ hu ht).symm
  have hmixed : HasDerivAt (fun t ↦ deriv (fun s ↦ f s t) u)
      (realRegularizedJet x u v).duv v := by
    apply hj.2.2.congr_of_eventuallyEq
    filter_upwards [hfst] with t ht
    exact ht.deriv
  have h := logKernel_mixed_scaled hp hu huv
    (hfst.mono fun _ ht ↦ ht.differentiableAt) hsnd hmixed
  rw [(hfst.self_of_nhds).deriv, ← heq u v hu huv] at h
  simpa only [realCorner, cornerFormula, realRegularizedJet, add_sub_cancel] using h.symm

#print axioms realRegularizedJet_isAt
#print axioms regularized_corner_eq_mixed


/-- The six-box bound transfers to the kernel once its primitive jets satisfy
the certified enclosures and realize the regularization on the open chamber. -/
theorem six_box_logKernel_lt_of_encloses {p : ℕ} (hp : 11 ≤ p) {x : ℝ → ℝ → CornerInputs ℝ}
    {u v : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v) (hd₁ : v - u ≤ 1 / 2)
    (hx : PrimitiveJetsAt x u v) (hV : Radicand (x u v).atV) (hD : Radicand (x u v).atD)
    (hNegU : Radicand (x u v).atNegU) (hNegV : Radicand (x u v).atNegV)
    (heq : ∀ s t : ℝ, 0 < s → s < t →
      (realRegularizedJet x s t).value = F p (compositionMarginalVariance p / 2) s t)
    (hbox : ∀ i : Fin 6, Encloses (sixBox i).1 u → Encloses (sixBox i).2.1 (v-u) →
      Encloses (sixBox i).2.2 (3 / (p : ℝ)) → CornerEncloses (primitiveBounds i) (x u v)) :
    v ^ 2 * deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v < -1 / 9 := by
  have hp₀ : 0 < p := by omega
  have hp₁ : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hh₀ : 0 ≤ 3 / (p : ℝ) := by positivity
  have hh₁ : 3 / (p : ℝ) ≤ 35 / 128 := by
    refine (div_le_iff₀ (by positivity)).2 ?_
    linarith
  obtain ⟨i, hui, hdi, hhi⟩ := six_box_cover hu.le hu₁ (sub_nonneg.mpr huv.le) hd₁ hh₀ hh₁
  rw [← regularized_corner_eq_mixed hp₀ hu huv hx hV hD hNegU hNegV heq]
  exact six_box_regularized_lt i hui hdi (hbox i hui hdi hhi) hV hD hNegU hNegV

#print axioms six_box_logKernel_lt_of_encloses

def JetTaylorError (x p : MixedJet ℝ) : Prop :=
  |x.value-p.value| ≤ 1/(2:ℝ)^30 ∧ |x.du-p.du| ≤ 1/(2:ℝ)^30 ∧
  |x.dv-p.dv| ≤ 1/(2:ℝ)^30 ∧ |x.duv-p.duv| ≤ 1/(2:ℝ)^30

def CornerTaylorError (x t : CornerInputs ℝ) : Prop :=
  JetTaylorError x.joint t.joint ∧ JetTaylorError x.prime t.prime ∧
  JetTaylorError x.firstDifference t.firstDifference ∧ JetTaylorError x.secondDifference t.secondDifference ∧
  JetTaylorError x.atV t.atV ∧ JetTaylorError x.atD t.atD ∧
  JetTaylorError x.atNegU t.atNegU ∧ JetTaylorError x.atNegV t.atNegV

private noncomputable def inputsOf (joint : ℕ → ℕ → ℝ → ℝ → ℝ) (marginal : ℕ → ℝ → ℝ) (u v : ℝ) :
    CornerInputs ℝ :=
  ⟨⟨joint 0 0 u v, joint 1 0 u v, joint 0 1 u v, joint 1 1 u v⟩,
    affineMarginalJet marginal 1 0 1 u v,
    weightedMarginalJet marginal (fun _ ↦ 1) 1 u v,
    weightedMarginalJet marginal (fun r ↦ 1-r) 2 u v,
    affineMarginalJet marginal 0 0 1 u v, affineMarginalJet marginal 0 (-1) 1 u v,
    affineMarginalJet marginal 0 (-1) 0 u v, affineMarginalJet marginal 0 0 (-1) u v⟩

/-- The eight actual small-corner primitives, continued by their integrals. -/
noncomputable def integralCornerInputs (p : ℕ) : ℝ → ℝ → CornerInputs ℝ :=
  inputsOf (integralJointDerivative p) (integralMarginalDerivative p (compositionMarginalVariance p / 2))

/-- Use the same primitive formulas with the corresponding Taylor polynomials in place
of the integral moments. The weights in D and Q are integrated exactly. -/
noncomputable def taylorCornerInputs (p : ℕ) : ℝ → ℝ → CornerInputs ℝ :=
  inputsOf (jointTaylorPolynomial p) (marginalTaylorPolynomial p)

theorem integralCornerInputs_isAt (p : ℕ) (u v : ℝ) :
    PrimitiveJetsAt (integralCornerInputs p) u v := by
  have hj : MixedJet.IsAt
      (fun s t ↦ ⟨integralJointDerivative p 0 0 s t, integralJointDerivative p 1 0 s t,
        integralJointDerivative p 0 1 s t, integralJointDerivative p 1 1 s t⟩) u v :=
    ⟨Eventually.of_forall (hasDerivAt_integralJointDerivative_fst p 0 0 u),
      hasDerivAt_integralJointDerivative_snd p 0 0 u v,
      hasDerivAt_integralJointDerivative_snd p 1 0 u v⟩
  exact ⟨hj, continuedMarginalJet_isAt p 1 0 1 u v,
    integralMarginalJet_isAt p continuous_const 1 u v,
    integralMarginalJet_isAt p (continuous_const.sub continuous_id) 2 u v,
    continuedMarginalJet_isAt p 0 0 1 u v, continuedMarginalJet_isAt p 0 (-1) 1 u v,
    continuedMarginalJet_isAt p 0 (-1) 0 u v, continuedMarginalJet_isAt p 0 0 (-1) u v⟩

private theorem affineJet_error {p k : ℕ} (hp : 0 < p) (hk : k + 2 ≤ 4)
    {a b u v : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |a*u+b*v| ≤ 1) :
    JetTaylorError
      (affineMarginalJet (integralMarginalDerivative p (compositionMarginalVariance p / 2)) k a b u v)
      (affineMarginalJet (marginalTaylorPolynomial p) k a b u v) := by
  have h₀ := integralMarginalDerivative_sub_taylor_le hp (show k ≤ 4 by omega) ht
  have h₁ := integralMarginalDerivative_sub_taylor_le hp (show k + 1 ≤ 4 by omega) ht
  have h₂ := integralMarginalDerivative_sub_taylor_le hp hk ht
  have hab : |a*b| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ ha (abs_nonneg _) hb
  simp only [JetTaylorError, affineMarginalJet, ← mul_sub, abs_mul]
  exact ⟨h₀, (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans (by simpa using h₁),
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (by simpa using h₁),
    by
      rw [← abs_mul a b]
      exact (mul_le_mul_of_nonneg_right hab (abs_nonneg _)).trans (by simpa using h₂)⟩

private theorem weightedJet_error {p k : ℕ} (hp : 0 < p) (hk : k + 2 ≤ 4)
    {w : ℝ → ℝ} (hc : Continuous w) (hw : ∀ r ∈ Icc (0:ℝ) 1, |w r| ≤ 1)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    JetTaylorError
      (weightedMarginalJet (integralMarginalDerivative p (compositionMarginalVariance p / 2)) w k u v)
      (weightedMarginalJet (marginalTaylorPolynomial p) w k u v) := by
  exact ⟨weightedMarginalIntegral_sub_taylor_le hp hc hw (k := k) (a := 0) (b := 0) (by omega) hu huv hv,
    weightedMarginalIntegral_sub_taylor_le hp hc hw (k := k) (a := 1) (b := 0) (by omega) hu huv hv,
    weightedMarginalIntegral_sub_taylor_le hp hc hw (k := k) (a := 0) (b := 1) (by omega) hu huv hv,
    weightedMarginalIntegral_sub_taylor_le hp hc hw (k := k) (a := 1) (b := 1) (by omega) hu huv hv⟩

theorem integralCornerInputs_sub_taylor_le {p : ℕ} (hp : 0 < p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    CornerTaylorError (integralCornerInputs p u v) (taylorCornerInputs p u v) := by
  have hV : |v| ≤ 1 := abs_le.mpr ⟨by linarith, hv⟩
  have hU : |u| ≤ 1 := abs_le.mpr ⟨by linarith, huv.trans hv⟩
  have hD : |v-u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hj (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :=
    integralJointDerivative_sub_jointTaylorPolynomial_le hp ha hb hu huv hv
  exact ⟨⟨hj 0 0 (by decide) (by decide), hj 1 0 (by decide) (by decide),
      hj 0 1 (by decide) (by decide), hj 1 1 (by decide) (by decide)⟩,
    affineJet_error hp (by decide) (by norm_num) (by norm_num) (by simpa using hV),
    weightedJet_error hp (by decide) continuous_const (by simp) hu huv hv,
    weightedJet_error (w := fun r ↦ 1 - r) hp (by decide) (continuous_const.sub continuous_id)
      (fun r hr ↦ abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩) hu huv hv,
    affineJet_error hp (by decide) (by norm_num) (by norm_num) (by simpa using hV),
    affineJet_error hp (by decide) (by norm_num) (by norm_num)
      (by simpa only [neg_one_mul, one_mul, sub_eq_add_neg, add_comm] using hD),
    affineJet_error hp (by decide) (by norm_num) (by norm_num) (by simpa using hU),
    affineJet_error hp (by decide) (by norm_num) (by norm_num) (by simpa using hV)⟩

theorem realRegularizedJet_integral_value {p : ℕ} (hp : 0 < p)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    (realRegularizedJet (integralCornerInputs p) u v).value =
      F p (compositionMarginalVariance p / 2) u v := by
  let c := compositionMarginalVariance p / 2
  have hc : c ≠ 0 := (half_pos (compositionMarginalVariance_pos p)).ne'
  have hv := hu.trans huv
  have hd : 0 < v - u := sub_pos.mpr huv
  have hG (t : ℝ) (ht : t ≠ 0) :
      integralMarginalDerivative p c 0 t = G p c t := by
    simpa only [iteratedDeriv_zero] using (iteratedDeriv_G_eq_integral hp hc ht 0).symm
  have hP : integralMarginalDerivative p c 1 v = GPrime p c v := by
    rw [← (hasDerivAt_G p hc hv.ne').deriv]
    simpa only [iteratedDeriv_one] using (iteratedDeriv_G_eq_integral hp hc hv.ne' 1).symm
  have hA := A_eq_integralJointDerivative (p := p) (v := v) hu.ne'
  change A p c u v = integralJointDerivative p 0 0 u v at hA
  obtain ⟨hD,hQ⟩ := D_Q_eq_weightedMarginalIntegral hp hu huv
  change D p c u v =
    weightedMarginalIntegral (integralMarginalDerivative p c) (fun _ ↦ 1) 1 0 0 u v at hD
  change Q p c u v =
    weightedMarginalIntegral (integralMarginalDerivative p c) (fun r ↦ 1 - r) 2 0 0 u v at hQ
  have hV' := hG v hv.ne'
  have hD' := hG (v-u) hd.ne'
  have hU' := hG (-u) (neg_ne_zero.mpr hu.ne')
  have hW' := hG (-v) (neg_ne_zero.mpr hv.ne')
  simp only [realRegularizedJet, regularizedJet, integralCornerInputs, inputsOf, affineMarginalJet,
    weightedMarginalJet, MixedJet.mul, MixedJet.add, MixedJet.sub, MixedJet.reciprocal,
    MixedJet.sqrtFrom, zero_mul, one_mul, neg_one_mul, zero_add, add_zero,
    show -u + v = v-u by ring]
  change _ = F p c u v
  rw [← hA, hP, ← hD, ← hQ, hV', hD', hU', hW']
  simp only [F, R, div_eq_mul_inv, one_mul, pow_two]
  ring

#print axioms integralCornerInputs_sub_taylor_le
#print axioms realRegularizedJet_integral_value

private def shrink (a : Bounds) : Bounds :=
  (a.1 + 1 / (2 : ℚ)^30, a.2 - 1 / (2 : ℚ)^30)

private def shrinkJet (a : MixedJet Bounds) : MixedJet Bounds :=
  ⟨shrink a.value, shrink a.du, shrink a.dv, shrink a.duv⟩

/-- Rational input intervals before adding the Taylor remainder to each component. -/
def taylorPrimitiveBounds (i : Fin 6) : CornerInputs Bounds :=
  let a := primitiveBounds i
  ⟨shrinkJet a.joint, shrinkJet a.prime, shrinkJet a.firstDifference, shrinkJet a.secondDifference,
    shrinkJet a.atV, shrinkJet a.atD, shrinkJet a.atNegU, shrinkJet a.atNegV⟩

private theorem enlarge_sound {a : Bounds} {x t : ℝ} (hb : Encloses (shrink a) t)
    (h : |x-t| ≤ 1 / (2 : ℝ)^30) : Encloses a x := by
  rw [abs_le] at h
  simp only [Encloses, shrink, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
    Rat.cast_pow, Rat.cast_ofNat] at hb
  exact ⟨by linarith [hb.1, h.1], by linarith [hb.2, h.2]⟩

private theorem enlarge_jet_sound {a : MixedJet Bounds} {x t : MixedJet ℝ}
    (hb : JetEncloses (shrinkJet a) t) (h : JetTaylorError x t) : JetEncloses a x :=
  ⟨enlarge_sound hb.1 h.1, enlarge_sound hb.2.1 h.2.1, enlarge_sound hb.2.2.1 h.2.2.1,
    enlarge_sound hb.2.2.2 h.2.2.2⟩

theorem integralCornerInputs_enclosed_of_taylor {p : ℕ} (hp : 0 < p) (i : Fin 6)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hb : CornerEncloses (taylorPrimitiveBounds i) (taylorCornerInputs p u v)) :
    CornerEncloses (primitiveBounds i) (integralCornerInputs p u v) := by
  have he := integralCornerInputs_sub_taylor_le hp hu huv hv
  rcases hb with ⟨hj, hpr, hf, hs, hv₀, hd₀, hnu, hnv⟩
  rcases he with ⟨hj', hpr', hf', hs', hv₀', hd₀', hnu', hnv'⟩
  exact ⟨enlarge_jet_sound hj hj', enlarge_jet_sound hpr hpr', enlarge_jet_sound hf hf',
    enlarge_jet_sound hs hs', enlarge_jet_sound hv₀ hv₀', enlarge_jet_sound hd₀ hd₀',
    enlarge_jet_sound hnu hnu', enlarge_jet_sound hnv hnv'⟩

/-- The remaining box checks involve only the Taylor polynomials, including the
polynomial integrals used to present their divided differences. -/
def TaylorBoxesEnclose : Prop :=
  ∀ (p : ℕ), 11 ≤ p → ∀ (i : Fin 6) (u d : ℝ),
    Encloses (sixBox i).1 u → Encloses (sixBox i).2.1 d →
    Encloses (sixBox i).2.2 (3 / (p : ℝ)) →
    CornerEncloses (taylorPrimitiveBounds i) (taylorCornerInputs p u (u+d))

theorem logKernel_small_corner_lt_of_taylorBoxes
    (hbox : TaylorBoxesEnclose) {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v) (hd : v-u ≤ 1 / 2) :
    v^2 * deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v < -1/9 := by
  have hp₀ : 0 < p := by omega
  have hv : v ≤ 1 := by linarith
  have hV : |v| ≤ 1 := abs_le.mpr ⟨by linarith, hv⟩
  have hU : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hD : |v-u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hV' : Radicand (integralCornerInputs p u v).atV := by
    simpa [Radicand, integralCornerInputs, inputsOf, affineMarginalJet] using
      integralMarginalDerivative_zero_mem hp₀ hV
  have hD' : Radicand (integralCornerInputs p u v).atD := by
    simpa [Radicand, integralCornerInputs, inputsOf, affineMarginalJet, sub_eq_add_neg, add_comm] using
      integralMarginalDerivative_zero_mem hp₀ hD
  have hU' : Radicand (integralCornerInputs p u v).atNegU := by
    simpa [Radicand, integralCornerInputs, inputsOf, affineMarginalJet] using
      integralMarginalDerivative_zero_mem hp₀ (show |-u| ≤ 1 by simpa using hU)
  have hW' : Radicand (integralCornerInputs p u v).atNegV := by
    simpa [Radicand, integralCornerInputs, inputsOf, affineMarginalJet] using
      integralMarginalDerivative_zero_mem hp₀ (show |-v| ≤ 1 by simpa using hV)
  apply six_box_logKernel_lt_of_encloses hp hu hu₁ huv hd (integralCornerInputs_isAt p u v)
    hV' hD' hU' hW' (fun _ _ hs hst ↦ realRegularizedJet_integral_value hp₀ hs hst)
  intro i hui hdi hhi
  apply integralCornerInputs_enclosed_of_taylor hp₀ i hu.le huv.le hv
  simpa only [add_sub_cancel] using hbox p hp i u (v-u) hui hdi hhi

#print axioms logKernel_small_corner_lt_of_taylorBoxes

end RefinedBMV.PositiveCenter.SmallCorner
