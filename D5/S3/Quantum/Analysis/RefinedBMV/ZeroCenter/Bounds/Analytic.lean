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

def intervalConstant {n : ℕ} (q : ℚ) : Expr n := .const q q q

private def intervalAdd {n : ℕ} (a b : Expr n) : Expr n :=
  .add (roundDown ((bounds a).1 + (bounds b).1))
    (roundUp ((bounds a).2 + (bounds b).2)) a b

private def intervalNeg {n : ℕ} (a : Expr n) : Expr n :=
  .neg (-(bounds a).2) (-(bounds a).1) a

private def intervalMul {n : ℕ} (a b : Expr n) : Expr n :=
  let (a₁, a₂) := bounds a
  let (b₁, b₂) := bounds b
  let p := a₁*b₁
  let q := a₁*b₂
  let r := a₂*b₁
  let s := a₂*b₂
  .mul (roundDown (min (min p q) (min r s))) (roundUp (max (max p q) (max r s))) a b

private def intervalInv {n : ℕ} (a : Expr n) : Expr n :=
  .inv (roundDown (1 / (bounds a).2)) (roundUp (1 / (bounds a).1)) a

private instance {n : ℕ} : Zero (Expr n) := ⟨intervalConstant 0⟩
private instance {n k : ℕ} : OfNat (Expr n) k := ⟨intervalConstant k⟩
private instance {n : ℕ} : Add (Expr n) := ⟨intervalAdd⟩
private instance {n : ℕ} : Neg (Expr n) := ⟨intervalNeg⟩
private instance {n : ℕ} : Sub (Expr n) := ⟨fun a b ↦ intervalAdd a (intervalNeg b)⟩
private instance {n : ℕ} : Mul (Expr n) := ⟨intervalMul⟩
private instance {n : ℕ} : Div (Expr n) := ⟨fun a b ↦ intervalMul a (intervalInv b)⟩

theorem value_zero {n : ℕ} (x : Fin n → ℝ) : value x (0 : Expr n) = 0 := by
  change ((0 : ℚ) : ℝ) = 0
  exact Rat.cast_zero

theorem value_1 {n : ℕ} (x : Fin n → ℝ) : value x (1 : Expr n) = 1 := by
  change ((1 : ℚ) : ℝ) = 1
  norm_num

theorem value_2 {n : ℕ} (x : Fin n → ℝ) : value x (2 : Expr n) = 2 := by
  change ((2 : ℚ) : ℝ) = 2
  norm_num

theorem value_3 {n : ℕ} (x : Fin n → ℝ) : value x (3 : Expr n) = 3 := by
  change ((3 : ℚ) : ℝ) = 3
  norm_num

theorem value_4 {n : ℕ} (x : Fin n → ℝ) : value x (4 : Expr n) = 4 := by
  change ((4 : ℚ) : ℝ) = 4
  norm_num

theorem value_9 {n : ℕ} (x : Fin n → ℝ) : value x (9 : Expr n) = 9 := by
  change ((9 : ℚ) : ℝ) = 9
  norm_num

theorem value_add {n : ℕ} (x : Fin n → ℝ) (a b : Expr n) :
    value x (a + b) = value x a + value x b := rfl

theorem value_neg {n : ℕ} (x : Fin n → ℝ) (a : Expr n) :
    value x (-a) = -value x a := rfl

theorem value_sub {n : ℕ} (x : Fin n → ℝ) (a b : Expr n) :
    value x (a - b) = value x a - value x b := by
  change value x a + -value x b = _
  exact (sub_eq_add_neg _ _).symm

theorem value_mul {n : ℕ} (x : Fin n → ℝ) (a b : Expr n) :
    value x (a * b) = value x a * value x b := rfl

theorem value_div {n : ℕ} (x : Fin n → ℝ) (a b : Expr n) :
    value x (a / b) = value x a / value x b := by
  change value x a * (1 / value x b) = _
  rw [one_div, div_eq_mul_inv]

def inputExpr {n : ℕ} (b : Fin n → ℚ × ℚ) (i : Fin n) : Expr n :=
  .input i (b i).1 (b i).2

private def analyticInputs (b : ZeroCenterRectangle) (r : ℚ × ℚ) : Fin 7 → ℚ × ℚ :=
  ![(b.hLo, b.hHi), geometricBounds b, expInput b 0 3,
    expInput b 3 3, expInput b 2 0, expInput b 1 3, r]

noncomputable def analyticPoint (c h : ℝ) : Fin 7 → ℝ :=
  ![h, zeroCenterGeometric c h, Real.exp (-3*h*c), Real.exp (-(3*(1+h))*c),
    Real.exp (-2*c), Real.exp (-(1+3*h)*c), Real.sqrt (rationalizedRadicand c h)]

private def radicandExpr (box : Fin 7 → ℚ × ℚ) : Expr 7 :=
  let v := inputExpr box
  (zeroCenterRadicandJet (v 0) (v 1) (v 2) (v 3) (v 4)).value

def curvatureExpr (box : Fin 7 → ℚ × ℚ) : Expr 7 :=
  let v := inputExpr box
  zeroCenterCurvature (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)

private theorem radicandExpr_value (box : Fin 7 → ℚ × ℚ) (c h : ℝ) (hh : h ≠ 0) :
    value (analyticPoint c h) (radicandExpr box) = rationalizedRadicand c h := by
  simp only [radicandExpr, inputExpr, value, zeroCenterRadicandJet, zeroCenterAB,
    zeroCenterGeometricJet, CurvatureJet.sub, CurvatureJet.mul, CurvatureJet.add,
    CurvatureJet.scale, CurvatureJet.const, CurvatureJet.exponential, value_zero, value_1, value_2, value_3, value_4, value_9,
    value_add, value_neg, value_sub, value_mul, value_div]
  change (zeroCenterRadicandJet h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
    (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c))).value = _
  exact zeroCenterRadicandJet_value c h hh

theorem curvatureExpr_value (box : Fin 7 → ℚ × ℚ) (c h : ℝ) :
    value (analyticPoint c h) (curvatureExpr box) =
      zeroCenterCurvature h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
        (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
        (Real.sqrt (rationalizedRadicand c h)) := by
  simp only [curvatureExpr, inputExpr, value, zeroCenterCurvature, zeroCenterQuotientJet,
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
  parametersValid b ∧ analyticCandidatesValid b box ∧ check box rad = true ∧
    r.1 ≤ r.2 ∧ 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1^2 ≤ (bounds rad).1 ∧ (bounds rad).2 ≤ r.2^2

private instance (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) :
    Decidable (analyticLeafValid b box) := by
  unfold analyticLeafValid
  infer_instance

def leafValid (b : ZeroCenterRectangle) (box : Fin 7 → ℚ × ℚ) : Prop :=
  let e := curvatureExpr box
  analyticLeafValid b box ∧ check box e = true ∧ 0 < (bounds e).1

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
  have hr := checked_expression_encloses box _ (hin ((box 6).1 : ℝ)
    ⟨le_rfl, (Rat.cast_le (K := ℝ)).mpr hrle⟩) _ hrCheck
  have hsame : value (Function.update (analyticPoint c h) 6 ((box 6).1 : ℝ))
      (radicandExpr box) = value (analyticPoint c h) (radicandExpr box) := rfl
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
  have he := checked_expression_encloses box _ (analyticLeaf_sound ha hch hh) _ hc
  rw [curvatureExpr_value] at he
  exact (by exact_mod_cast hp : (0 : ℝ) < _).trans_le he.1

end RefinedBMV.FourSpectrumLift
