/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Bounds/Analytic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational geometric, exponential and square-root bounds on rectangles. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Curvature
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Box
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace RefinedBMV.FourSpectrumLift

open D5.S0.Certificates.BoxCover.RationalIntervalExpression

private theorem geometric_mono_c {x y h : ℝ} (hxy : x ≤ y) (hh : 0 ≤ h) :
    zeroCenterGeometric x h ≤ zeroCenterGeometric y h := by
  unfold zeroCenterGeometric
  split
  · linarith
  · apply div_le_div_of_nonneg_right _ hh
    apply sub_le_sub_left
    exact Real.exp_monotone (by nlinarith [mul_nonneg hh (sub_nonneg.mpr hxy)])

private theorem geometric_anti_h {c h k : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (hhk : h ≤ k) :
    zeroCenterGeometric c k ≤ zeroCenterGeometric c h := by
  by_cases hk : k = 0
  · have : h = k := le_antisymm hhk (hk ▸ hh)
    rw [this]
  have hk' : 0 < k := lt_of_le_of_ne (hh.trans hhk) (Ne.symm hk)
  by_cases hz : h = 0
  · simp only [hz, zeroCenterGeometric, ite_eq_left rfl, ite_eq_right hk, ite_true]
    apply (div_le_iff₀ hk').mpr
    linarith [Real.add_one_le_exp (-3 * k * c)]
  have hh' : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
  have ht : 0 ≤ h / k := div_nonneg hh hk'.le
  have ht' : 0 ≤ 1 - h / k := sub_nonneg.mpr ((div_le_one hk').mpr hhk)
  have hconv := convexOn_exp.2 (Set.mem_univ (-3 * k * c)) (Set.mem_univ (0 : ℝ))
    ht ht' (by ring : h/k + (1-h/k) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have harg : h / k * (-3 * k * c) = -3 * h * c := by
    field_simp
    <;> ring
  rw [harg] at hconv
  simp only [zeroCenterGeometric, ite_eq_right hk, ite_eq_right hz]
  apply (div_le_div_iff₀ hk' hh').mpr
  calc
    (1 - Real.exp (-3 * k * c)) * h =
        (h / k * (1 - Real.exp (-3 * k * c))) * k := by field_simp
    _ ≤ (1 - Real.exp (-3 * h * c)) * k := by
      apply mul_le_mul_of_nonneg_right _ hk'.le
      linarith

structure ZeroCenterRectangle where
  cLo : ℚ
  cHi : ℚ
  hLo : ℚ
  hHi : ℚ
  deriving DecidableEq

namespace ZeroCenterRectangle

def Holds (b : ZeroCenterRectangle) (c h : ℝ) : Prop :=
  (b.cLo : ℝ) ≤ c ∧ c ≤ (b.cHi : ℝ) ∧ (b.hLo : ℝ) ≤ h ∧ h ≤ (b.hHi : ℝ)

private def geomPoint (c h : ℚ) : ℚ × ℚ :=
  if h = 0 then (3*c, 3*c) else
    let e := compactExpBounds (-3*h*c) (-3*h*c)
    ((1 - e.2) / h, (1 - e.1) / h)

private theorem geomPoint_sound {c h : ℚ} (hh : 0 ≤ h) (he : |-3*h*c| ≤ 256) :
    ((geomPoint c h).1 : ℝ) ≤ zeroCenterGeometric (c : ℝ) (h : ℝ) ∧
      zeroCenterGeometric (c : ℝ) (h : ℝ) ≤ ((geomPoint c h).2 : ℝ) := by
  by_cases hz : h = 0
  · subst h
    simp [geomPoint, zeroCenterGeometric]
  have hz' : (h : ℝ) ≠ 0 := by exact_mod_cast hz
  have hh' : 0 ≤ (h : ℝ) := by exact_mod_cast hh
  have harg : ((-3*h*c : ℚ) : ℝ) = -3 * (h : ℝ) * (c : ℝ) := by push_cast; ring
  have hab := compactExpBounds_sound he he
    (show ((-3*h*c : ℚ) : ℝ) ≤ -3 * (h : ℝ) * (c : ℝ) ∧
      -3 * (h : ℝ) * (c : ℝ) ≤ ((-3*h*c : ℚ) : ℝ) by rw [harg]; exact ⟨le_rfl, le_rfl⟩)
  simp only [geomPoint, ite_eq_right hz, zeroCenterGeometric, ite_eq_right hz', Rat.cast_div,
    Rat.cast_sub, Rat.cast_one]
  exact ⟨div_le_div_of_nonneg_right (sub_le_sub_left hab.2 _) hh',
    div_le_div_of_nonneg_right (sub_le_sub_left hab.1 _) hh'⟩

private def geometricBounds (b : ZeroCenterRectangle) : ℚ × ℚ :=
  ((geomPoint b.cLo b.hHi).1, (geomPoint b.cHi b.hLo).2)

private theorem geometricBounds_sound {b : ZeroCenterRectangle} {c h : ℝ}
    (hb : b.Holds c h) (hc : 0 ≤ b.cLo) (hh : 0 ≤ b.hLo) (hh' : 0 ≤ b.hHi)
    (hlo : |-3*b.hHi*b.cLo| ≤ 256) (hhi : |-3*b.hLo*b.cHi| ≤ 256) :
    ((geometricBounds b).1 : ℝ) ≤ zeroCenterGeometric c h ∧
      zeroCenterGeometric c h ≤ ((geometricBounds b).2 : ℝ) := by
  rcases hb with ⟨hcl, hcu, hhl, hhu⟩
  have hcl' : 0 ≤ (b.cLo : ℝ) := by exact_mod_cast hc
  have hhl' : 0 ≤ (b.hLo : ℝ) := by exact_mod_cast hh
  have hh0 := hhl'.trans hhl
  exact ⟨(geomPoint_sound hh' hlo).1.trans
    ((geometric_anti_h hcl' hh0 hhu).trans (geometric_mono_c hcl hh0)),
    ( (geometric_anti_h (hcl'.trans hcl) hhl' hhl).trans
      (geometric_mono_c hcu hhl')).trans (geomPoint_sound hh hhi).2⟩

def argument (b : ZeroCenterRectangle) (a k : ℚ) : ℚ × ℚ :=
  (-(a+k*b.hHi)*b.cHi, -(a+k*b.hLo)*b.cLo)

theorem argument_sound {b : ZeroCenterRectangle} {c h : ℝ}
    (hb : b.Holds c h) (hc : 0 ≤ b.cLo) (hh : 0 ≤ b.hLo)
    {a k : ℚ} (ha : 0 ≤ a) (hk : 0 ≤ k) :
    ((argument b a k).1 : ℝ) ≤ -((a : ℝ) + (k : ℝ)*h)*c ∧
      -((a : ℝ) + (k : ℝ)*h)*c ≤ ((argument b a k).2 : ℝ) := by
  rcases hb with ⟨hcl, hcu, hhl, hhu⟩
  have hc' : 0 ≤ (b.cLo : ℝ) := by exact_mod_cast hc
  have hh' : 0 ≤ (b.hLo : ℝ) := by exact_mod_cast hh
  have ha' : 0 ≤ (a : ℝ) := by exact_mod_cast ha
  have hk' : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hl : 0 ≤ (a : ℝ) + (k : ℝ) * b.hLo := by positivity
  have hm : (a : ℝ) + (k : ℝ)*b.hLo ≤ (a : ℝ) + (k : ℝ)*h :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hhl hk')
  have hu : (a : ℝ) + (k : ℝ)*h ≤ (a : ℝ) + (k : ℝ)*b.hHi :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hhu hk')
  simp only [argument, Rat.cast_mul, Rat.cast_neg, Rat.cast_add]
  exact ⟨by simpa only [neg_mul] using neg_le_neg (mul_le_mul hu hcu (hc'.trans hcl)
      (hl.trans (hm.trans hu))),
    by simpa only [neg_mul] using neg_le_neg (mul_le_mul hm hcl hc' (hl.trans hm))⟩

private def expInput (b : ZeroCenterRectangle) (a k : ℚ) : ℚ × ℚ :=
  let e := argument b a k
  compactExpBounds e.1 e.2

private theorem expInput_sound {b : ZeroCenterRectangle} {c h : ℝ}
    (hb : b.Holds c h) (hc : 0 ≤ b.cLo) (hh : 0 ≤ b.hLo)
    {a k : ℚ} (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hl : |(argument b a k).1| ≤ 256) (hu : |(argument b a k).2| ≤ 256) :
    ((expInput b a k).1 : ℝ) ≤ Real.exp (-((a : ℝ) + (k : ℝ)*h)*c) ∧
      Real.exp (-((a : ℝ) + (k : ℝ)*h)*c) ≤ ((expInput b a k).2 : ℝ) :=
  compactExpBounds_sound hl hu (argument_sound hb hc hh ha hk)

end ZeroCenterRectangle

open ZeroCenterRectangle

/-- An interval expression generated over a fixed input box.
The guards check input order and strict separation from zero at reciprocals.
The constructor proof transfers their result to the general interval checker. -/
structure IntervalExpr {n : ℕ} (box : Fin n → ℚ × ℚ) where
  expr : Expr n
  guards : Bool
  checked : guards = true ↔ check box expr = true

section IntervalExpr

variable {n : ℕ} {box : Fin n → ℚ × ℚ}

def intervalBounds (e : IntervalExpr box) : ℚ × ℚ := bounds e.expr

noncomputable def intervalValue (x : Fin n → ℝ) (e : IntervalExpr box) : ℝ :=
  value x e.expr

theorem guarded_expression_encloses (box : Fin n → ℚ × ℚ) (x : Fin n → ℝ)
    (hx : ∀ i, ((box i).1 : ℝ) ≤ x i ∧ x i ≤ ((box i).2 : ℝ))
    (e : IntervalExpr box) (he : e.guards = true) :
    ((intervalBounds e).1 : ℝ) ≤ intervalValue x e ∧
      intervalValue x e ≤ ((intervalBounds e).2 : ℝ) :=
  checked_expression_encloses box x hx e.expr (e.checked.mp he)

private theorem checked_bounds_ordered (e : Expr n) (he : check box e = true) :
    (bounds e).1 ≤ (bounds e).2 := by
  cases e <;> simp only [bounds, check, Bool.and_eq_true_iff, decide_eq_true_eq] at he ⊢
  · exact he.1
  · exact he.1
  · exact (of_decide_eq_true he.2.2).1
  · exact (of_decide_eq_true he.2).1
  · exact (of_decide_eq_true he.2.2).1
  · exact (of_decide_eq_true he.2).1
  · exact (of_decide_eq_true he.2).1

private theorem intervalBounds_ordered (e : IntervalExpr box) (he : e.guards = true) :
    (intervalBounds e).1 ≤ (intervalBounds e).2 :=
  checked_bounds_ordered e.expr (e.checked.mp he)

def intervalConstant (q : ℚ) : IntervalExpr box := by
  refine ⟨.const q q q, true, ?_⟩
  simp only [check, decide_eq_true_eq, eq_self, le_refl, and_true]

private def intervalAdd (a b : IntervalExpr box) : IntervalExpr box := by
  let lo := (intervalBounds a).1 + (intervalBounds b).1
  let hi := (intervalBounds a).2 + (intervalBounds b).2
  refine ⟨.add (roundDown lo) (roundUp hi) a.expr b.expr, a.guards && b.guards, ?_⟩
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq, ← a.checked, ← b.checked]
  constructor
  · rintro ⟨ha, hb⟩
    have h := add_le_add (intervalBounds_ordered a ha) (intervalBounds_ordered b hb)
    exact ⟨ha, hb, (roundDown_le lo).trans (h.trans (le_roundUp hi)),
      roundDown_le lo, le_roundUp hi⟩
  · rintro ⟨ha, hb, _⟩
    exact ⟨ha, hb⟩

private def intervalNeg (a : IntervalExpr box) : IntervalExpr box := by
  refine ⟨.neg (-(intervalBounds a).2) (-(intervalBounds a).1) a.expr, a.guards, ?_⟩
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq, ← a.checked]
  constructor
  · intro ha
    exact ⟨ha, neg_le_neg (intervalBounds_ordered a ha), le_rfl, le_rfl⟩
  · exact And.left

private theorem rounded_mul_corners (p q r s : ℚ) :
    let lo := roundDown (min (min p q) (min r s))
    let hi := roundUp (max (max p q) (max r s))
    lo ≤ hi ∧ lo ≤ p ∧ lo ≤ q ∧ lo ≤ r ∧ lo ≤ s ∧
      p ≤ hi ∧ q ≤ hi ∧ r ≤ hi ∧ s ≤ hi := by
  dsimp only
  have hlo := roundDown_le (min (min p q) (min r s))
  have hhi := le_roundUp (max (max p q) (max r s))
  have hloLeft := hlo.trans (min_le_left (min p q) (min r s))
  have hloRight := hlo.trans (min_le_right (min p q) (min r s))
  have hhiLeft := (le_max_left (max p q) (max r s)).trans hhi
  have hhiRight := (le_max_right (max p q) (max r s)).trans hhi
  have hp := hloLeft.trans (min_le_left p q)
  have hp' := (le_max_left p q).trans hhiLeft
  exact ⟨hp.trans hp', hp, hloLeft.trans (min_le_right p q),
    hloRight.trans (min_le_left r s), hloRight.trans (min_le_right r s), hp',
    (le_max_right p q).trans hhiLeft, (le_max_left r s).trans hhiRight,
    (le_max_right r s).trans hhiRight⟩

private def intervalMul (a b : IntervalExpr box) : IntervalExpr box := by
  let p := (intervalBounds a).1 * (intervalBounds b).1
  let q := (intervalBounds a).1 * (intervalBounds b).2
  let r := (intervalBounds a).2 * (intervalBounds b).1
  let s := (intervalBounds a).2 * (intervalBounds b).2
  refine ⟨.mul (roundDown (min (min p q) (min r s))) (roundUp (max (max p q) (max r s)))
    a.expr b.expr, a.guards && b.guards, ?_⟩
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq, ← a.checked, ← b.checked]
  exact ⟨fun h ↦ ⟨h.1, h.2, rounded_mul_corners p q r s⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩

private def intervalInv (a : IntervalExpr box) : IntervalExpr box := by
  let lo := (intervalBounds a).1
  let hi := (intervalBounds a).2
  refine ⟨.inv (roundDown (1 / hi)) (roundUp (1 / lo)) a.expr,
    a.guards && decide (hi < 0 ∨ 0 < lo), ?_⟩
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq, ← a.checked]
  constructor
  · rintro ⟨ha, hsign⟩
    have hle : lo ≤ hi := intervalBounds_ordered a ha
    have hinv : 1 / hi ≤ 1 / lo := by
      rcases hsign with hneg | hpos
      · have h := one_div_le_one_div_of_le (neg_pos.mpr hneg) (neg_le_neg hle)
        simpa only [one_div, inv_neg, neg_neg] using neg_le_neg h
      · exact one_div_le_one_div_of_le hpos hle
    exact ⟨ha, (roundDown_le _).trans (hinv.trans (le_roundUp _)),
      hsign, roundDown_le _, le_roundUp _⟩
  · rintro ⟨ha, _, hsign, _⟩
    exact ⟨ha, hsign⟩

private instance : Zero (IntervalExpr box) := ⟨intervalConstant 0⟩
private instance {k : ℕ} : OfNat (IntervalExpr box) k := ⟨intervalConstant k⟩
private instance : Add (IntervalExpr box) := ⟨intervalAdd⟩
private instance : Neg (IntervalExpr box) := ⟨intervalNeg⟩
private instance : Sub (IntervalExpr box) := ⟨fun a b ↦ intervalAdd a (intervalNeg b)⟩
private instance : Mul (IntervalExpr box) := ⟨intervalMul⟩
private instance : Div (IntervalExpr box) := ⟨fun a b ↦ intervalMul a (intervalInv b)⟩

def inputExpr (box : Fin n → ℚ × ℚ) (i : Fin n) : IntervalExpr box := by
  refine ⟨.input i (box i).1 (box i).2, decide ((box i).1 ≤ (box i).2), ?_⟩
  simp only [check, decide_eq_true_eq, le_refl, and_true]

theorem intervalValue_input (x : Fin n → ℝ) (box : Fin n → ℚ × ℚ) (i : Fin n) :
    intervalValue x (inputExpr box i) = x i := rfl

theorem value_zero (x : Fin n → ℝ) :
    intervalValue x (0 : IntervalExpr box) = 0 := by
  change ((0 : ℚ) : ℝ) = 0
  exact Rat.cast_zero

theorem value_1 (x : Fin n → ℝ) :
    intervalValue x (1 : IntervalExpr box) = 1 := by
  change ((1 : ℚ) : ℝ) = 1
  norm_num

theorem value_2 (x : Fin n → ℝ) :
    intervalValue x (2 : IntervalExpr box) = 2 := by
  change ((2 : ℚ) : ℝ) = 2
  norm_num

theorem value_3 (x : Fin n → ℝ) :
    intervalValue x (3 : IntervalExpr box) = 3 := by
  change ((3 : ℚ) : ℝ) = 3
  norm_num

theorem value_4 (x : Fin n → ℝ) :
    intervalValue x (4 : IntervalExpr box) = 4 := by
  change ((4 : ℚ) : ℝ) = 4
  norm_num

theorem value_9 (x : Fin n → ℝ) :
    intervalValue x (9 : IntervalExpr box) = 9 := by
  change ((9 : ℚ) : ℝ) = 9
  norm_num

theorem value_add (x : Fin n → ℝ) (a b : IntervalExpr box) :
    intervalValue x (a + b) = intervalValue x a + intervalValue x b := rfl

theorem value_neg (x : Fin n → ℝ) (a : IntervalExpr box) :
    intervalValue x (-a) = -intervalValue x a := rfl

theorem value_sub (x : Fin n → ℝ) (a b : IntervalExpr box) :
    intervalValue x (a - b) = intervalValue x a - intervalValue x b := by
  change intervalValue x a + -intervalValue x b = _
  exact (sub_eq_add_neg _ _).symm

theorem value_mul (x : Fin n → ℝ) (a b : IntervalExpr box) :
    intervalValue x (a * b) = intervalValue x a * intervalValue x b := rfl

theorem value_div (x : Fin n → ℝ) (a b : IntervalExpr box) :
    intervalValue x (a / b) = intervalValue x a / intervalValue x b := by
  change intervalValue x a * (1 / intervalValue x b) = _
  rw [one_div, div_eq_mul_inv]

end IntervalExpr

private def analyticInputs (b : ZeroCenterRectangle) (r : ℚ × ℚ) : Fin 7 → ℚ × ℚ :=
  ![(b.hLo, b.hHi), geometricBounds b, expInput b 0 3,
    expInput b 3 3, expInput b 2 0, expInput b 1 3, r]

noncomputable def analyticPoint (c h : ℝ) : Fin 7 → ℝ :=
  ![h, zeroCenterGeometric c h, Real.exp (-3*h*c), Real.exp (-(3*(1+h))*c),
    Real.exp (-2*c), Real.exp (-(1+3*h)*c), Real.sqrt (rationalizedRadicand c h)]

private def radicandExpr (box : Fin 7 → ℚ × ℚ) : IntervalExpr box :=
  let v := inputExpr box
  (zeroCenterRadicandJet (v 0) (v 1) (v 2) (v 3) (v 4)).value

def curvatureExpr (box : Fin 7 → ℚ × ℚ) : IntervalExpr box :=
  let v := inputExpr box
  zeroCenterCurvature (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)

private theorem radicandExpr_value (box : Fin 7 → ℚ × ℚ) (c h : ℝ) (hh : h ≠ 0) :
    intervalValue (analyticPoint c h) (radicandExpr box) = rationalizedRadicand c h := by
  simp only [radicandExpr, intervalValue_input, zeroCenterRadicandJet, zeroCenterAB,
    zeroCenterGeometricJet, CurvatureJet.sub, CurvatureJet.mul, CurvatureJet.add,
    CurvatureJet.scale, CurvatureJet.const, CurvatureJet.exponential, value_zero, value_1, value_2, value_3, value_4, value_9,
    value_add, value_neg, value_sub, value_mul, value_div]
  change (zeroCenterRadicandJet h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
    (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c))).value = _
  exact zeroCenterRadicandJet_value c h hh

theorem curvatureExpr_value (box : Fin 7 → ℚ × ℚ) (c h : ℝ) :
    intervalValue (analyticPoint c h) (curvatureExpr box) =
      zeroCenterCurvature h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
        (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
        (Real.sqrt (rationalizedRadicand c h)) := by
  simp only [curvatureExpr, intervalValue_input, zeroCenterCurvature, zeroCenterQuotientJet,
    zeroCenterRadicandJet, zeroCenterAB, zeroCenterV, zeroCenterGeometricJet,
    CurvatureJet.quot, CurvatureJet.sqrtFrom, CurvatureJet.sub, CurvatureJet.mul,
    CurvatureJet.add, CurvatureJet.scale, CurvatureJet.const, CurvatureJet.exponential, value_zero,
    value_1, value_2, value_3, value_4, value_9, value_add, value_neg, value_sub, value_mul, value_div]
  rfl

def parametersValid (b : ZeroCenterRectangle) : Prop :=
  0 ≤ b.cLo ∧ 0 ≤ b.hLo ∧ 0 ≤ b.hHi ∧ |-3*b.hHi*b.cLo| ≤ 256 ∧ |-3*b.hLo*b.cHi| ≤ 256 ∧
    (∀ i : Fin 4, let a : Fin 4 → ℚ := ![0, 3, 2, 1]; let k : Fin 4 → ℚ := ![3, 3, 0, 3]
      |(argument b (a i) (k i)).1| ≤ 256 ∧ |(argument b (a i) (k i)).2| ≤ 256)

private instance (b : ZeroCenterRectangle) : Decidable (parametersValid b) := by
  unfold parametersValid
  infer_instance

private def analyticCandidatesValid (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) : Prop :=
  ∀ i, i = 6 ∨
    (box i).1 ≤ (analyticInputs b (0, 0) i).1 ∧
    (analyticInputs b (0, 0) i).2 ≤ (box i).2

private instance (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) :
    Decidable (analyticCandidatesValid b box) := by
  unfold analyticCandidatesValid
  infer_instance

def analyticLeafValid (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) : Prop :=
  let r := box 6
  let rad := radicandExpr box
  parametersValid b ∧ analyticCandidatesValid b box ∧ rad.guards = true ∧
    r.1 ≤ r.2 ∧ 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1^2 ≤ (intervalBounds rad).1 ∧ (intervalBounds rad).2 ≤ r.2^2

private instance (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) :
    Decidable (analyticLeafValid b box) := by
  unfold analyticLeafValid
  infer_instance

def leafValid (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) : Prop :=
  let e := curvatureExpr box
  analyticLeafValid b box ∧ e.guards = true ∧ 0 < (intervalBounds e).1

private instance (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) :
    Decidable (leafValid b box) := by
  unfold leafValid
  infer_instance

theorem analyticLeaf_sound {b : ZeroCenterRectangle} {box : Fin 7 → ℚ × ℚ}
    (hb : analyticLeafValid b box) {c h : ℝ} (hch : b.Holds c h) (hh : 0 < h) :
    ∀ i, ((box i).1 : ℝ) ≤ analyticPoint c h i ∧ analyticPoint c h i ≤ ((box i).2 : ℝ) := by
  rcases hb with ⟨⟨hc, hhl, hhu, hgl, hgu, ha⟩, hboxes, hrCheck, hrle, hrl, hru, hrl', hru'⟩
  have hgeom := geometricBounds_sound hch hc hhl hhu hgl hgu
  have hq := expInput_sound hch hc hhl (a := 0) (k := 3)
    (by norm_num) (by norm_num) (ha 0).1 (ha 0).2
  have hz := expInput_sound hch hc hhl (a := 3) (k := 3)
    (by norm_num) (by norm_num) (ha 1).1 (ha 1).2
  have he₀ := expInput_sound hch hc hhl (a := 2) (k := 0)
    (by norm_num) (by norm_num) (ha 2).1 (ha 2).2
  have hu := expInput_sound hch hc hhl (a := 1) (k := 3)
    (by norm_num) (by norm_num) (ha 3).1 (ha 3).2
  push_cast at hq hz he₀ hu
  rw [show -(0 + 3*h)*c = -3*h*c by ring] at hq
  rw [show -(3 + 3*h)*c = -(3*(1+h))*c by ring] at hz
  rw [show -(2 + 0*h)*c = -2*c by ring] at he₀
  have hbase (i : Fin 7) (hi : i ≠ 6) :
      ((analyticInputs b (0, 0) i).1 : ℝ) ≤ analyticPoint c h i ∧
        analyticPoint c h i ≤ ((analyticInputs b (0, 0) i).2 : ℝ) := by
    fin_cases i
    · exact ⟨hch.2.2.1, hch.2.2.2⟩
    · exact hgeom
    · exact hq
    · exact hz
    · exact he₀
    · exact hu
    · exact (hi rfl).elim
  have hin (x : ℝ) (hx : ((box 6).1 : ℝ) ≤ x ∧ x ≤ ((box 6).2 : ℝ)) :
      ∀ i, ((box i).1 : ℝ) ≤ (Function.update (analyticPoint c h) 6 x) i ∧
        (Function.update (analyticPoint c h) 6 x) i ≤ ((box i).2 : ℝ) := by
    intro i
    by_cases hi : i = 6
    · subst i
      simpa using hx
    · obtain ⟨hl, hu⟩ := (hboxes i).resolve_left hi
      rw [Function.update_of_ne hi]
      exact ⟨((Rat.cast_le (K := ℝ)).mpr hl).trans (hbase i hi).1,
        (hbase i hi).2.trans ((Rat.cast_le (K := ℝ)).mpr hu)⟩
  have hr := guarded_expression_encloses box _ (hin ((box 6).1 : ℝ)
    ⟨le_rfl, (Rat.cast_le (K := ℝ)).mpr hrle⟩) (radicandExpr box) hrCheck
  have hsame : intervalValue (Function.update (analyticPoint c h) 6 ((box 6).1 : ℝ))
      (radicandExpr box) = intervalValue (analyticPoint c h) (radicandExpr box) := rfl
  rw [hsame, radicandExpr_value _ c h hh.ne'] at hr
  have hsqrt := sqrt_box_of_square_bounds hrl hru hrl' hru' hr
  have hpoint : Function.update (analyticPoint c h) 6
      (Real.sqrt (rationalizedRadicand c h)) = analyticPoint c h :=
    Function.update_eq_self _ _
  rw [← hpoint]
  exact hin _ hsqrt

theorem leaf_positive {b : ZeroCenterRectangle} {box : Fin 7 → ℚ × ℚ}
    (hb : leafValid b box) {c h : ℝ} (hch : b.Holds c h) (hh : 0 < h) :
    0 < zeroCenterCurvatureAt h c := by
  obtain ⟨ha, hc, hp⟩ := hb
  have he := guarded_expression_encloses box _ (analyticLeaf_sound ha hch hh)
    (curvatureExpr box) hc
  rw [curvatureExpr_value] at he
  exact (by exact_mod_cast hp : (0 : ℝ) < _).trans_le he.1

end RefinedBMV.FourSpectrumLift
