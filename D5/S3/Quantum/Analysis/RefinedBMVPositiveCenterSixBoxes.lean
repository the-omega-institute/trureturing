/-
theory: D5
plane: F
domain: Quantum/Analysis
-/
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMixedJet
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMarginalTaylor
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentTable
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterJointTaylorReplay
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterWeightedTaylorReplay
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

private local instance : Add DyadicInterval := ⟨dyadicAdd⟩
private local instance : Mul DyadicInterval := ⟨dyadicMul⟩

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

private def dyadicScalar (a : DyadicInterval) : MixedJet DyadicInterval :=
  ⟨a, dyadicPoint 0, dyadicPoint 0, dyadicPoint 0⟩

private def dyadicJet (a : MixedJet DyadicInterval) : MixedJet Bounds :=
  ⟨dyadicBounds a.value, dyadicBounds a.du, dyadicBounds a.dv, dyadicBounds a.duv⟩

private theorem dyadicScalar_encloses {a : DyadicInterval} {x : ℝ}
    (hx : Encloses (dyadicBounds a) x) :
    JetEncloses (dyadicJet (dyadicScalar a)) ⟨x, 0, 0, 0⟩ := by
  have hz : Encloses (dyadicBounds (dyadicPoint 0)) (0 : ℝ) := by
    simpa using dyadicPoint_encloses 0
  exact ⟨hx, hz, hz, hz⟩

private theorem dyadicJet_add (a b : MixedJet DyadicInterval) :
    dyadicJet (a.add b) = (dyadicJet a).add (dyadicJet b) := by
  change (⟨dyadicBounds (dyadicAdd a.value b.value), dyadicBounds (dyadicAdd a.du b.du),
    dyadicBounds (dyadicAdd a.dv b.dv), dyadicBounds (dyadicAdd a.duv b.duv)⟩ : MixedJet Bounds) = _
  simp only [dyadicAdd_bounds]
  rfl

private theorem dyadicJet_mul {a b : MixedJet DyadicInterval} {x y : MixedJet ℝ}
    (hx : JetEncloses (dyadicJet a) x) (hy : JetEncloses (dyadicJet b) y) :
    JetEncloses (dyadicJet (a.mul b)) (x.mul y) := by
  exact ⟨dyadicMul_encloses hx.1 hy.1,
    dyadicAdd_encloses (dyadicMul_encloses hx.2.1 hy.1) (dyadicMul_encloses hx.1 hy.2.1),
    dyadicAdd_encloses (dyadicMul_encloses hx.2.2.1 hy.1) (dyadicMul_encloses hx.1 hy.2.2.1),
    dyadicAdd_encloses (dyadicAdd_encloses (dyadicAdd_encloses
      (dyadicMul_encloses hx.2.2.2 hy.1) (dyadicMul_encloses hx.2.1 hy.2.2.1))
      (dyadicMul_encloses hx.2.2.1 hy.2.1)) (dyadicMul_encloses hx.1 hy.2.2.2)⟩

private theorem dyadicJet_add_sound {a b : MixedJet DyadicInterval} {x y : MixedJet ℝ}
    (hx : JetEncloses (dyadicJet a) x) (hy : JetEncloses (dyadicJet b) y) :
    JetEncloses (dyadicJet (a.add b)) (x.add y) :=
  by rw [dyadicJet_add]; exact jet_add hx hy

/-- Integer endpoints of the six leaves on the common dyadic grid. -/
private def dyadicSixBox (i : Fin 6) :
    DyadicInterval × DyadicInterval × DyadicInterval :=
  ![
    ((0, 4398046511104), (0, 8796093022208), (0, 4810363371520)),
    ((4398046511104, 8796093022208), (0, 4398046511104), (0, 4810363371520)),
    ((4398046511104, 6597069766656), (4398046511104, 8796093022208), (0, 4810363371520)),
    ((6597069766656, 8796093022208), (4398046511104, 6597069766656), (0, 4810363371520)),
    ((6597069766656, 8796093022208), (6597069766656, 8796093022208), (0, 2405181685760)),
    ((6597069766656, 8796093022208), (6597069766656, 8796093022208), (2405181685760, 4810363371520))
  ] i

private theorem dyadicSixBox_bounds (i : Fin 6) :
    (dyadicBounds (dyadicSixBox i).1, dyadicBounds (dyadicSixBox i).2.1,
      dyadicBounds (dyadicSixBox i).2.2) = sixBox i := by
  fin_cases i <;> decide +kernel

private def momentBoxIndex (i : Fin 6) : Fin 3 :=
  if i.val = 4 then 1 else if i.val = 5 then 2 else 0

private def momentBox (j : Fin 3) : DyadicInterval :=
  ![(0, 4810363371520), (0, 2405181685760), (2405181685760, 4810363371520)] j

private theorem momentBox_eq (i : Fin 6) :
    momentBox (momentBoxIndex i) = (dyadicSixBox i).2.2 := by
  fin_cases i <;> decide +kernel

private def exactDegreeBounds (j : Fin 3) : Array (Array DyadicInterval) :=
  ![
    #[
      #[(0, 0), (0, 0), (17592186044416, 17592186044416), (2345624805922, 2666315697358), (1759218604441, 2240254941595), (335089257988, 478791705435), (108205906225, 171817652759), (20943078624, 37347467604), (4537667035, 8977664044), (789772661, 1738312394), (134860733, 327838261), (20476592, 54977426), (2946214, 8731748)],
      #[],
      #[(17592186044416, 17592186044416), (-3999473546037, -3518437208883), (5277655813324, 6720764824782), (335089257988, 478791705435), (554991583544, 878076024463), (94243853809, 168063604211), (35952284971, 70859706237), (6917562333, 15215268328), (1594529849, 3865842910), (282265074, 756328967), (49753081, 146904939)],
      #[(2345624805922, 2666315697358), (-4480509883189, -3518437208883), (335089257988, 478791705435), (-897063785139, -568953635960), (-93368669006, -52357696560), (-86891822107, -44329516421), (-16748878888, -7626242266), (-5628223844, -2332297392), (-1137801192, -425533415), (-254278618, -86723630)],
      #[(1759218604441, 2240254941595), (-1196979263587, -837723144972), (554991583544, 878076024463), (-93368669006, -52357696560), (48518132146, 94907880042), (3077997919, 6748547741), (2641683781, 6338873789), (388919641, 1037656912), (108809742, 317150431)],
      #[(335089257988, 478791705435), (-515452958272, -324617718676), (94243853809, 168063604211), (-86891822107, -44329516421), (3077997919, 6748547741), (-6202441371, -2594085875), (-436449650, -163744932), (-316708770, -109347326)],
      #[(108205906225, 171817652759), (-130716136609, -73300775185), (35952284971, 70859706237), (-16748878888, -7626242266), (2641683781, 6338873789), (-436449650, -163744932), (107424618, 310220985)],
      #[(20943078624, 37347467604), (-35910656173, -18150668141), (6917562333, 15215268328), (-5628223844, -2332297392), (388919641, 1037656912), (-316708770, -109347326)],
      #[(4537667035, 8977664044), (-7822405770, -3553976978), (1594529849, 3865842910), (-1137801192, -425533415), (108809742, 317150431)],
      #[(789772661, 1738312394), (-1639191300, -674303667), (282265074, 756328967), (-254278618, -86723630)],
      #[(134860733, 327838261), (-302375835, -112621256), (49753081, 146904939)],
      #[(20476592, 54977426), (-52390482, -17677284)],
      #[(2946214, 8731748)]
    ],
    #[
      #[(0, 0), (0, 0), (17592186044416, 17592186044416), (2345624805922, 2505970251641), (1759218604441, 1999736773019), (335089257988, 405374608219), (108205906225, 138902619101), (20943078624, 28623315283), (4537667035, 6578242536), (789772661, 1215866875), (134860733, 219981098), (20476592, 35393476), (2946214, 5392724)],
      #[],
      #[(17592186044416, 17592186044416), (-3758955377461, -3518437208883), (5277655813324, 5999210319054), (335089257988, 405374608219), (554991583544, 711640449338), (94243853809, 128804918771), (35952284971, 52052167480), (6917562333, 10647069665), (1594529849, 2598362371), (282265074, 487603359), (49753081, 90966145)],
      #[(2345624805922, 2505970251641), (-3999473546037, -3518437208883), (335089257988, 405374608219), (-728767803172, -568953635960), (-71558288206, -52357696560), (-64061106953, -44329516421), (-11731539465, -7626242266), (-3794016574, -2332297392), (-734501753, -425533415), (-158230976, -86723630)],
      #[(1759218604441, 1999736773019), (-1013436520547, -837723144972), (554991583544, 711640449338), (-71558288206, -52357696560), (48518132146, 70065576690), (3077997919, 4732070425), (2641683781, 4288316693), (388919641, 670742326), (108809742, 198085746)],
      #[(335089257988, 405374608219), (-416707857302, -324617718676), (94243853809, 128804918771), (-64061106953, -44329516421), (3077997919, 4732070425), (-4205495107, -2594085875), (-282291868, -163744932), (-198562263, -109347326)],
      #[(108205906225, 138902619101), (-100181603489, -73300775185), (35952284971, 52052167480), (-11731539465, -7626242266), (2641683781, 4288316693), (-282291868, -163744932), (107424618, 194841110)],
      #[(20943078624, 28623315283), (-26312970140, -18150668141), (6917562333, 10647069665), (-3794016574, -2332297392), (388919641, 670742326), (-198562263, -109347326)],
      #[(4537667035, 6578242536), (-5471400935, -3553976978), (1594529849, 2598362371), (-734501753, -425533415), (108809742, 198085746)],
      #[(789772661, 1215866875), (-1099905486, -674303667), (282265074, 487603359), (-158230976, -86723630)],
      #[(134860733, 219981098), (-194664110, -112621256), (49753081, 90966145)],
      #[(20476592, 35393476), (-32356336, -17677284)],
      #[(2946214, 5392724)]
    ],
    #[
      #[(0, 0), (0, 0), (17592186044416, 17592186044416), (2505970251639, 2666315697358), (1988775658563, 2229293827141), (405160523950, 478363536902), (138657732343, 171337635692), (28564207126, 37235105159), (6557001171, 8938849104), (1212031074, 1732146861), (219199259, 326750554), (35284574, 54834663), (5373621, 8680906)],
      #[],
      #[(17592186044416, 17592186044416), (-3999473546037, -3758955377458), (5966326975691, 6687881481422), (405160523950, 478363536902), (710178446135, 875225191397), (128538932068, 167557973211), (51847966526, 70479969590), (10611579996, 15157621837), (2586893309, 3848719581), (485985886, 754718611), (90601740, 146149770)],
      #[(2505970251639, 2666315697358), (-4458587654282, -3977551317128), (405160523950, 478363536902), (-893762204339, -727068230548), (-93087762895, -71410517815), (-86296021337, -63745883175), (-16676592356, -11687877399), (-5592361729, -3771595436), (-1134303957, -731447773), (-253414875, -157448334)],
      #[(1988775658563, 2229293827141), (-1195908842254, -1012901309878), (710178446135, 875225191397), (-93087762895, -71410517815), (69694841500, 94204047209), (4712390630, 6715411102), (4255201971, 6283465159), (667346647, 1033344001), (196623728, 315370822)],
      #[(405160523950, 478363536902), (-514012907072, -415973197033), (128538932068, 167557973211), (-86296021337, -63745883175), (4712390630, 6715411102), (-6138891044, -4168206348), (-434420008, -280746460), (-313794813, -196477357)],
      #[(138657732343, 171337635692), (-130322868054, -99974724942), (51847966526, 70479969590), (-16676592356, -11687877399), (4255201971, 6283465159), (-434420008, -280746460), (192512517, 306844984)],
      #[(28564207126, 37235105159), (-35755396411, -26228004687), (10611579996, 15157621837), (-5592361729, -3771595436), (667346647, 1033344001), (-313794813, -196477357)],
      #[(6557001171, 8938849104), (-7794660873, -5454139839), (2586893309, 3848719581), (-1134303957, -731447773), (196623728, 315370822)],
      #[(1212031074, 1732146861), (-1633752767, -1095996299), (485985886, 754718611), (-253414875, -157448334)],
      #[(219199259, 326750554), (-301590640, -194065162), (90601740, 146149770)],
      #[(35284574, 54834663), (-52085425, -32241727)],
      #[(5373621, 8680906)]
    ]
  ] j


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

private def exactDegreeBound (i : Fin 6) (a b : ℕ) : DyadicInterval :=
  ((exactDegreeBounds (momentBoxIndex i)).getD a #[]).getD b (0, 0)

private def coarseDegreeBound (a b : ℕ) : DyadicInterval :=
  let d := a.factorial * b.factorial
  let n : ℤ := 2 ^ (a+b-1)
  ((dyadicFraction (-n) d).1, (dyadicFraction n d).2)

private def coefficientBound (i : Fin 6) (a b : ℕ) : DyadicInterval :=
  if a+b ≤ 12 then exactDegreeBound i a b else coarseDegreeBound a b

private def dyadicContained (outer inner : DyadicInterval) : Prop :=
  outer.1 ≤ inner.1 ∧ inner.2 ≤ outer.2

private instance (outer inner : DyadicInterval) : Decidable (dyadicContained outer inner) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

private theorem dyadicContained_encloses {outer inner : DyadicInterval} {x : ℝ}
    (hc : dyadicContained outer inner) (hx : Encloses (dyadicBounds inner) x) :
    Encloses (dyadicBounds outer) x := by
  have h₁ : (gridValue outer.1 : ℝ) ≤ (gridValue inner.1 : ℝ) :=
    Rat.cast_le.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hc.1) grid_pos.le)
  have h₂ : (gridValue inner.2 : ℝ) ≤ (gridValue outer.2 : ℝ) :=
    Rat.cast_le.mpr (div_le_div_of_nonneg_right (by exact_mod_cast hc.2) grid_pos.le)
  exact ⟨h₁.trans hx.1, hx.2.trans h₂⟩

private theorem coarseDegreeBound_encloses {p a b : ℕ} (hp : 0 < p)
    (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    Encloses (dyadicBounds (coarseDegreeBound a b))
      (momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)) := by
  have hc : |momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)| ≤
      (2 : ℝ) ^ (a+b-1) / ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
    rcases ha with rfl | ha
    · obtain ⟨r, rfl⟩ : ∃ r, b = r+2 := ⟨b-2, by omega⟩
      simpa [show r+2-1 = r+1 by omega] using normalized_moment_abs_bound_marginal hp r
    · obtain ⟨r, rfl⟩ : ∃ r, a = r+2 := ⟨a-2, by omega⟩
      simpa [show r+2+b-1 = r+b+1 by omega] using normalized_moment_abs_bound_joint hp r b
  obtain ⟨hlo, hhi⟩ := abs_le.mp hc
  have hlo' := (dyadicFraction_encloses (-(2 : ℤ)^(a+b-1)) (a.factorial*b.factorial)).1
  have hhi' := (dyadicFraction_encloses ((2 : ℤ)^(a+b-1)) (a.factorial*b.factorial)).2
  refine ⟨hlo'.trans ?_, hhi.trans ?_⟩
  · simpa only [Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Nat.cast_mul, neg_div] using hlo
  · push_cast at hhi'
    exact hhi'


private def checkExactDegreeBound (i : Fin 6) (a b : ℕ) : Prop :=
  dyadicContained (exactDegreeBound i a b)
    (dyadicHorner (dyadicSixBox i).2.2 (certifiedMomentDenominator a b)
      (stagedNumerators a b))

private def checkExactDegreeRow (j : Fin 3) (a : ℕ) : Bool :=
  (List.range (13-a)).all fun b ↦
    if 2 ≤ a+b ∧ (a = 0 ∨ 2 ≤ a) then
      decide (dyadicContained (((exactDegreeBounds j).getD a #[]).getD b (0, 0))
        (dyadicHorner (momentBox j) (certifiedMomentDenominator a b)
          (stagedNumerators a b)))
    else true

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
set_option cbv.maxSteps 5000000 in
private theorem exactDegreeRows_checked (j : Fin 3) :
    (List.range 13).all (checkExactDegreeRow j) = true := by
  fin_cases j <;> decide_cbv

private theorem exactDegreeBound_checked (i : Fin 6) {a b : ℕ}
    (hcut : a+b ≤ 12) (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    checkExactDegreeBound i a b := by
  have hrow := List.all_eq_true.mp (exactDegreeRows_checked (momentBoxIndex i)) a
    (List.mem_range.mpr (by omega))
  have he := List.all_eq_true.mp hrow b (List.mem_range.mpr (by omega))
  simpa [hab, ha, checkExactDegreeBound, exactDegreeBound, momentBox_eq] using he

private theorem coefficientBound_encloses {p a b : ℕ} (hp : 0 < p) (i : Fin 6)
    (hh : Encloses (dyadicBounds (dyadicSixBox i).2.2) (3 / (p : ℝ)))
    (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
    Encloses (dyadicBounds (coefficientBound i a b))
      (momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)) := by
  unfold coefficientBound
  split_ifs with hc
  · rw [← certifiedMomentCoeffs_eq, certifiedMomentCoeffs, ← stagedNumerators_eq hc hab ha]
    exact dyadicContained_encloses (exactDegreeBound_checked i hc hab ha)
      (dyadicHorner_encloses hh _ _)
  · exact coarseDegreeBound_encloses hp hab ha

private theorem cornerJetHorner_encloses {x : MixedJet DyadicInterval} {t : MixedJet ℝ}
    (ht : JetEncloses (dyadicJet x) t)
    {z : MixedJet DyadicInterval} {z' : MixedJet ℝ} (hz : JetEncloses (dyadicJet z) z')
    (c : ℕ → MixedJet DyadicInterval) (c' : ℕ → MixedJet ℝ)
    (hc : ∀ i, JetEncloses (dyadicJet (c i)) (c' i)) (n start : ℕ) :
    JetEncloses (dyadicJet (cornerJetHorner x z c start n)) (cornerJetHorner t z' c' start n) := by
  induction n generalizing start with
  | zero => exact hz
  | succ n ih =>
    exact dyadicJet_add_sound (dyadicJet_mul (ih (start+1)) ht) (hc start)

private theorem marginalHorner_encloses {x : MixedJet DyadicInterval} {t : MixedJet ℝ}
    (ht : JetEncloses (dyadicJet x) t)
    {z : MixedJet DyadicInterval} {z' : MixedJet ℝ} (hz : JetEncloses (dyadicJet z) z')
    {c : List (MixedJet DyadicInterval)} {c' : List (MixedJet ℝ)}
    (hc : List.Forall₂ (fun a b ↦ JetEncloses (dyadicJet a) b) c c') :
    JetEncloses (dyadicJet (marginalHorner MixedJet.add MixedJet.mul z x c))
      (marginalHorner MixedJet.add MixedJet.mul z' t c') := by
  induction hc with
  | nil => exact hz
  | cons h _ ih => exact dyadicJet_add_sound (dyadicJet_mul ih ht) h

private theorem marginalDifferenceHorner_encloses
    {v d : MixedJet DyadicInterval} {v' d' : MixedJet ℝ}
    (hv : JetEncloses (dyadicJet v) v') (hd : JetEncloses (dyadicJet d) d')
    {z : MixedJet DyadicInterval} {z' : MixedJet ℝ} (hz : JetEncloses (dyadicJet z) z')
    {c : List (MixedJet DyadicInterval)} {c' : List (MixedJet ℝ)}
    (hc : List.Forall₂ (fun a b ↦ JetEncloses (dyadicJet a) b) c c') :
    let r := marginalDifferenceHorner MixedJet.add MixedJet.mul z v d c
    let r' := marginalDifferenceHorner MixedJet.add MixedJet.mul z' v' d' c'
    JetEncloses (dyadicJet r.atV) r'.atV ∧ JetEncloses (dyadicJet r.atD) r'.atD ∧
    JetEncloses (dyadicJet r.prime) r'.prime ∧
    JetEncloses (dyadicJet r.firstDifference) r'.firstDifference ∧
    JetEncloses (dyadicJet r.secondDifference) r'.secondDifference := by
  induction hc with
  | nil => exact ⟨hz, hz, hz, hz, hz⟩
  | cons h _ ih =>
    rcases ih with ⟨hV, hD, hP, hF, hS⟩
    exact ⟨dyadicJet_add_sound (dyadicJet_mul hV hv) h,
      dyadicJet_add_sound (dyadicJet_mul hD hd) h,
      dyadicJet_add_sound (dyadicJet_mul hP hv) hV,
      dyadicJet_add_sound (dyadicJet_mul hF hv) hD,
      dyadicJet_add_sound (dyadicJet_mul hS hv) hF⟩

private def dyadicCornerBounds (c : CornerInputs DyadicInterval) : CornerInputs Bounds :=
  ⟨dyadicJet c.joint, dyadicJet c.prime, dyadicJet c.firstDifference,
    dyadicJet c.secondDifference, dyadicJet c.atV, dyadicJet c.atD,
    dyadicJet c.atNegU, dyadicJet c.atNegV⟩

private def dyadicTaylorReplay (i : Fin 6) : CornerInputs DyadicInterval :=
  let ub := (dyadicSixBox i).1
  let db := (dyadicSixBox i).2.1
  let vb := dyadicAdd ub db
  let z := dyadicPoint 0
  let one := dyadicPoint 1
  let negOne := dyadicPoint (-1)
  let u : MixedJet DyadicInterval := ⟨ub, one, z, z⟩
  let v : MixedJet DyadicInterval := ⟨vb, z, one, z⟩
  let d : MixedJet DyadicInterval := ⟨db, negOne, one, z⟩
  let negU : MixedJet DyadicInterval := ⟨dyadicNeg ub, negOne, z, z⟩
  let negV : MixedJet DyadicInterval := ⟨dyadicNeg vb, z, negOne, z⟩
  let zero := dyadicScalar z
  let cs := List.ofFn (n := 23) fun k ↦ dyadicScalar (coefficientBound i 0 (k.val+2))
  let result := marginalDifferenceHorner MixedJet.add MixedJet.mul zero v d cs
  ⟨cornerJointHorner u v zero (fun a b ↦ dyadicScalar (coefficientBound i (a+2) b)) 23,
    result.prime, result.firstDifference, result.secondDifference, result.atV, result.atD,
    marginalHorner MixedJet.add MixedJet.mul zero negU cs,
    marginalHorner MixedJet.add MixedJet.mul zero negV cs⟩


private theorem forall₂_ofFn {α β : Type} {n : ℕ}
    {P : α → β → Prop} {f : Fin n → α} {g : Fin n → β}
    (h : ∀ i, P (f i) (g i)) : List.Forall₂ P (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [List.ofFn_succ] using List.Forall₂.cons (h 0) (ih (fun i ↦ h i.succ))

private theorem dyadicTaylorReplay_encloses {p : ℕ} (hp : 0 < p) (i : Fin 6)
    {u d : ℝ} (hu : Encloses (sixBox i).1 u) (hd : Encloses (sixBox i).2.1 d)
    (hh : Encloses (sixBox i).2.2 (3 / (p : ℝ))) :
    CornerEncloses (dyadicCornerBounds (dyadicTaylorReplay i)) (taylorCornerInputs p u (u+d)) := by
  have hboxes := dyadicSixBox_bounds i
  have hU : Encloses (dyadicBounds (dyadicSixBox i).1) u := by
    have e : dyadicBounds (dyadicSixBox i).1 = (sixBox i).1 := congrArg Prod.fst hboxes
    rwa [e]
  have hD : Encloses (dyadicBounds (dyadicSixBox i).2.1) d := by
    have e : dyadicBounds (dyadicSixBox i).2.1 = (sixBox i).2.1 :=
      congrArg (fun b ↦ b.2.1) hboxes
    rwa [e]
  have hH : Encloses (dyadicBounds (dyadicSixBox i).2.2) (3 / (p : ℝ)) := by
    have e : dyadicBounds (dyadicSixBox i).2.2 = (sixBox i).2.2 :=
      congrArg (fun b ↦ b.2.2) hboxes
    rwa [e]
  let v := u+d
  let ub := (dyadicSixBox i).1
  let db := (dyadicSixBox i).2.1
  let vb := dyadicAdd ub db
  have hV : Encloses (dyadicBounds vb) v := dyadicAdd_encloses hU hD
  have hnU : Encloses (dyadicBounds (dyadicNeg ub)) (-u) := by
    rw [dyadicNeg_bounds]
    exact encloses_neg hU
  have hnV : Encloses (dyadicBounds (dyadicNeg vb)) (-v) := by
    rw [dyadicNeg_bounds]
    exact encloses_neg hV
  let z := dyadicPoint 0
  let one := dyadicPoint 1
  let negOne := dyadicPoint (-1)
  have hz : Encloses (dyadicBounds z) (0 : ℝ) := by simpa using dyadicPoint_encloses 0
  have h1 : Encloses (dyadicBounds one) (1 : ℝ) := by simpa using dyadicPoint_encloses 1
  have hn1 : Encloses (dyadicBounds negOne) (-1 : ℝ) := by simpa using dyadicPoint_encloses (-1)
  let uJet : MixedJet DyadicInterval := ⟨ub, one, z, z⟩
  let vJet : MixedJet DyadicInterval := ⟨vb, z, one, z⟩
  let dJet : MixedJet DyadicInterval := ⟨db, negOne, one, z⟩
  let nUJet : MixedJet DyadicInterval := ⟨dyadicNeg ub, negOne, z, z⟩
  let nVJet : MixedJet DyadicInterval := ⟨dyadicNeg vb, z, negOne, z⟩
  have hUj : JetEncloses (dyadicJet uJet) (⟨u, 1, 0, 0⟩ : MixedJet ℝ) := ⟨hU, h1, hz, hz⟩
  have hVj : JetEncloses (dyadicJet vJet) (⟨v, 0, 1, 0⟩ : MixedJet ℝ) := ⟨hV, hz, h1, hz⟩
  have hDj : JetEncloses (dyadicJet dJet) (marginalAffineInput (-1) 1 u v) := by
    simpa [marginalAffineInput, v] using
      (show JetEncloses (dyadicJet dJet) (⟨d, -1, 1, 0⟩ : MixedJet ℝ) from ⟨hD, hn1, h1, hz⟩)
  have hnUj : JetEncloses (dyadicJet nUJet) (marginalAffineInput (-1) 0 u v) := by
    simpa [marginalAffineInput] using
      (show JetEncloses (dyadicJet nUJet) (⟨-u, -1, 0, 0⟩ : MixedJet ℝ) from ⟨hnU, hn1, hz, hz⟩)
  have hnVj : JetEncloses (dyadicJet nVJet) (marginalAffineInput 0 (-1) u v) := by
    simpa [marginalAffineInput] using
      (show JetEncloses (dyadicJet nVJet) (⟨-v, 0, -1, 0⟩ : MixedJet ℝ) from ⟨hnV, hz, hn1, hz⟩)
  have hvAffine : JetEncloses (dyadicJet vJet) (marginalAffineInput 0 1 u v) := by
    simpa [marginalAffineInput] using hVj
  have hzero : JetEncloses (dyadicJet (dyadicScalar z)) (marginalScalarJet 0) :=
    dyadicScalar_encloses hz
  let cr (a b : ℕ) := momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b)
  have hc (a b : ℕ) (hab : 2 ≤ a+b) (ha : a = 0 ∨ 2 ≤ a) :
      JetEncloses (dyadicJet (dyadicScalar (coefficientBound i a b))) (marginalScalarJet (cr a b)) :=
    dyadicScalar_encloses (coefficientBound_encloses hp i hH hab ha)
  let cs := List.ofFn (n := 23) fun k ↦ dyadicScalar (coefficientBound i 0 (k.val+2))
  have hcs : List.Forall₂ (fun a b ↦ JetEncloses (dyadicJet a) b)
      cs ((marginalTaylorMomentCoefficients p).map marginalScalarJet) := by
    unfold cs marginalTaylorMomentCoefficients
    rw [List.map_ofFn]
    exact forall₂_ofFn (fun k ↦ hc 0 (k.val+2) (by omega) (Or.inl rfl))
  have hJ := cornerJetHorner_encloses hUj hzero
    (fun a ↦ cornerJetHorner vJet (dyadicScalar z)
      (fun b ↦ dyadicScalar (coefficientBound i (a+2) b)) 0 (23-a))
    (fun a ↦ cornerJetHorner (⟨v, 0, 1, 0⟩ : MixedJet ℝ) (marginalScalarJet 0)
      (fun b ↦ marginalScalarJet (cr (a+2) b)) 0 (23-a))
    (fun a ↦ cornerJetHorner_encloses hVj hzero _ _
      (fun b ↦ hc (a+2) b (by omega) (Or.inr (by omega))) (23-a) 0) 23 0
  have hJ' : JetEncloses (dyadicJet (dyadicTaylorReplay i).joint)
      (taylorCornerInputs p u v).joint := by
    rw [show (taylorCornerInputs p u v).joint = _ from
      jointTaylorPolynomial_jet_eq_cornerJointHorner hp u v]
    exact hJ
  have hM := marginalDifferenceHorner_encloses hvAffine hDj hzero hcs
  obtain ⟨eV, eD, eP, eF, eS⟩ := marginalDifferenceHorner_taylor hp u v
  rcases hM with ⟨hMv, hMd, hMp, hMf, hMs⟩
  rw [eV] at hMv
  rw [eD] at hMd
  rw [eP] at hMp
  rw [eF] at hMf
  rw [eS] at hMs
  have hNu := marginalHorner_encloses hnUj hzero hcs
  have hNv := marginalHorner_encloses hnVj hzero hcs
  rw [marginalHorner_affineTaylor hp] at hNu hNv
  exact ⟨hJ', hMp, hMf, hMs, hMv, hMd, hNu, hNv⟩

private def BoundsContained (outer inner : Bounds) : Prop :=
  outer.1 ≤ inner.1 ∧ inner.2 ≤ outer.2

private def JetContained (outer inner : MixedJet Bounds) : Prop :=
  BoundsContained outer.value inner.value ∧ BoundsContained outer.du inner.du ∧
  BoundsContained outer.dv inner.dv ∧ BoundsContained outer.duv inner.duv

private def CornerContained (outer inner : CornerInputs Bounds) : Prop :=
  JetContained outer.joint inner.joint ∧ JetContained outer.prime inner.prime ∧
  JetContained outer.firstDifference inner.firstDifference ∧
  JetContained outer.secondDifference inner.secondDifference ∧
  JetContained outer.atV inner.atV ∧ JetContained outer.atD inner.atD ∧
  JetContained outer.atNegU inner.atNegU ∧ JetContained outer.atNegV inner.atNegV

private instance (a b : Bounds) : Decidable (BoundsContained a b) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

private instance (a b : MixedJet Bounds) : Decidable (JetContained a b) :=
  inferInstanceAs (Decidable (BoundsContained _ _ ∧ BoundsContained _ _ ∧
    BoundsContained _ _ ∧ BoundsContained _ _))

private instance (a b : CornerInputs Bounds) : Decidable (CornerContained a b) :=
  inferInstanceAs (Decidable (JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _ ∧
    JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _ ∧ JetContained _ _))

private theorem boundsContained_encloses {a b : Bounds} {x : ℝ}
    (hs : BoundsContained a b) (hx : Encloses b x) : Encloses a x :=
  ⟨(Rat.cast_le.mpr hs.1).trans hx.1, hx.2.trans (Rat.cast_le.mpr hs.2)⟩

private theorem jetContained_encloses {a b : MixedJet Bounds} {x : MixedJet ℝ}
    (hs : JetContained a b) (hx : JetEncloses b x) : JetEncloses a x :=
  ⟨boundsContained_encloses hs.1 hx.1, boundsContained_encloses hs.2.1 hx.2.1,
    boundsContained_encloses hs.2.2.1 hx.2.2.1, boundsContained_encloses hs.2.2.2 hx.2.2.2⟩

private theorem cornerContained_encloses {a b : CornerInputs Bounds} {x : CornerInputs ℝ}
    (hs : CornerContained a b) (hx : CornerEncloses b x) : CornerEncloses a x := by
  rcases hs with ⟨hJ, hP, hF, hS, hV, hD, hnU, hnV⟩
  rcases hx with ⟨eJ, eP, eF, eS, eV, eD, enU, enV⟩
  exact ⟨jetContained_encloses hJ eJ, jetContained_encloses hP eP, jetContained_encloses hF eF,
    jetContained_encloses hS eS, jetContained_encloses hV eV, jetContained_encloses hD eD,
    jetContained_encloses hnU enU, jetContained_encloses hnV enV⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
set_option cbv.maxSteps 5000000 in
private theorem dyadicTaylorReplay_checked (i : Fin 6) :
    CornerContained (taylorPrimitiveBounds i) (dyadicCornerBounds (dyadicTaylorReplay i)) := by
  fin_cases i <;> decide_cbv

/-- The original six leaves enclose every component of the Taylor jets. -/
theorem taylorBoxesEnclose : TaylorBoxesEnclose := by
  intro p hp i u d hu hd hh
  exact cornerContained_encloses (dyadicTaylorReplay_checked i)
    (dyadicTaylorReplay_encloses (by omega : 0 < p) i hu hd hh)

/-- For every natural degree at least eleven, the mixed derivative is uniformly
negative in the open ordered small corner. -/
theorem logKernel_small_corner_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v) (hd : v-u ≤ 1 / 2) :
    v^2 * deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v < -1/9 :=
  logKernel_small_corner_lt_of_taylorBoxes taylorBoxesEnclose hp hu hu₁ huv hd

#print axioms taylorBoxesEnclose
#print axioms logKernel_small_corner_lt

end RefinedBMV.PositiveCenter.SmallCorner
