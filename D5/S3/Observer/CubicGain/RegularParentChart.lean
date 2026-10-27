/- GID: D5/S3/Observer/CubicGain/RegularParentChart
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/RegularParentChart
   mirror-E: none(waiver:analytic-original-parent-chart)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.Constructions]
   utility: none
   digest: A regular source strip lifts analytically to original parent worlds and actual reads. -/

import D5.S3.Observer.CubicGain.CommonWordSensitivity
import Mathlib.Analysis.Analytic.Constructions

/-! Rational regular coordinates for the literal original parent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.RegularParentChart

open D5.S3.Observer.CubicGain
open CommonWordSensitivity

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- The parent equation determines the drift increment on the regular stratum. -/
def regularError (r b : ℝ) : ℝ :=
  -((24/5)*(b-1/8)*parentB b) / parentLambda r b

/-- Independent source coordinates are `(t,b)`, with `r=t*b`. -/
def chartCoordinates (x : ℝ × ℝ) : Coordinates :=
  (x.1*x.2,x.2,regularError (x.1*x.2) x.2)

/-- One whole gain in its original ordinary coefficient coordinates. -/
def chartWorld (x : ℝ × ℝ) : OriginalWorld :=
  encodeWorld (parentWorld (chartCoordinates x))

def chartSource (x : ℝ × ℝ) : Fin 8 → ℝ := sourceCoordinates (chartWorld x)

/-- The fifth read and actual eighth-M read of this same world. -/
def chartRead (x : ℝ × ℝ) : ℝ × ℝ :=
  ((originalResponse (chartWorld x)).1,futureRead (chartWorld x) [])

theorem strip_denominator (r b : ℝ)
    (hr : 9005/10000 ≤ r) (hr' : r ≤ 9006/10000)
    (hb : 12758/100000 ≤ b) (hb' : b ≤ 12759/100000) :
    parentLambda r b < 0 := by
  have h0 : 0 < b := by linarith
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b (by linarith) (by linarith) h0
  have hm : r*(1-r) ≤ (9006/10000 : ℝ)*(1-9005/10000) :=
    mul_le_mul hr' (by linarith) (by linarith) (by norm_num)
  have hj' : sourceJ r b < 83/100 := by
    unfold sourceJ
    have hbb : b*b ≤ (12759/100000 : ℝ)^2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 12759/100000-b)
        (by linarith : 0 ≤ 12759/100000+b)]
    have he : r*(1-r) < (83/100-b)*b := by nlinarith
    have hd := (div_lt_iff₀ h0).mpr he
    linarith
  have hn' : sourceN r b < 1731/1000 := by unfold sourceN; linarith
  have hT : 6/(1+b) ≤ (6 : ℝ)/(1+12758/100000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hU : 1/(1+2*b) ≤ (1 : ℝ)/(1+2*(12758/100000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hJ : (4 : ℝ)/(83/100) ≤ 4/sourceJ r b :=
    div_le_div_of_nonneg_left (by norm_num) hj hj'.le
  have hN : (4 : ℝ)/(1731/1000) ≤ 4/sourceN r b :=
    div_le_div_of_nonneg_left (by norm_num) hn hn'.le
  unfold parentLambda
  linarith

private theorem chart_parent (x : ℝ × ℝ)
    (hr : 0 < x.1*x.2) (hr' : x.1*x.2 < 1) (hb : 0 < x.2)
    (hl : parentLambda (x.1*x.2) x.2 ≠ 0) :
    StrictParent (chartCoordinates x) := by
  refine ⟨hr,hr',hb,?_⟩
  dsimp [parentEq,chartCoordinates,regularError]
  rw [div_mul_cancel₀ _ hl]
  ring

private theorem chart_unique (x : ℝ × ℝ)
    (hl : parentLambda (x.1*x.2) x.2 ≠ 0)
    (W : OriginalWorld) (hW : OriginalParent W)
    (hr : W.1 = x.1*x.2) (hb : W.2.1 = x.2) : W = chartWorld x := by
  obtain ⟨hC,hencode,_⟩ := original_coordinates W hW
  have he : W.2.2.1-24 = regularError (x.1*x.2) x.2 := by
    apply (eq_div_iff hl).mpr
    have hp := hC.2.2.2
    change (W.2.2.1-24)*parentLambda W.1 W.2.1 +
      (24/5)*(W.2.1-1/8)*parentB W.2.1 = 0 at hp
    rw [hr,hb] at hp
    linarith
  have hc : worldCoordinates (decodeWorld W) = chartCoordinates x := by
    simp only [worldCoordinates,decodeWorld,chartCoordinates]
    rw [hr,hb,he]
  rw [hc] at hencode
  exact hencode.symm

private theorem chart_analytic (x : ℝ × ℝ)
    (hb : x.2 ≠ 0) (hj : sourceJ (x.1*x.2) x.2 ≠ 0)
    (hn : sourceN (x.1*x.2) x.2 ≠ 0) (ht : 1+x.2 ≠ 0)
    (hu : 1+2*x.2 ≠ 0) (hl : parentLambda (x.1*x.2) x.2 ≠ 0) :
    AnalyticAt ℝ chartWorld x := by
  have hJ : AnalyticAt ℝ (fun y : ℝ × ℝ => sourceJ (y.1*y.2) y.2) x := by
    unfold sourceJ
    fun_prop (disch := exact hb)
  have hN : AnalyticAt ℝ (fun y : ℝ × ℝ => sourceN (y.1*y.2) y.2) x := by
    unfold sourceN
    fun_prop
  have hL : AnalyticAt ℝ (fun y : ℝ × ℝ => parentLambda (y.1*y.2) y.2) x := by
    unfold parentLambda
    fun_prop (disch := first | exact hj | exact hn | exact ht | exact hu)
  have hE : AnalyticAt ℝ (fun y : ℝ × ℝ => regularError (y.1*y.2) y.2) x := by
    unfold regularError parentB
    fun_prop (disch := first | exact ht | exact hu | exact hl)
  unfold chartWorld encodeWorld parentWorld chartCoordinates gainCoefficients parentGain
  dsimp
  apply AnalyticAt.prod (by fun_prop)
  apply AnalyticAt.prod (by fun_prop)
  apply AnalyticAt.prod (by fun_prop)
  apply AnalyticAt.pi
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals fun_prop (disch := first | exact hj | exact hn | exact ht)

/-- The lift contains every original parent world with the specified source.
The source and read maps are analytic in the genuine `(t,b)` chart. -/
theorem analytic_original_parent_chart (x : ℝ × ℝ)
    (hr : 9005/10000 ≤ x.1*x.2) (hr' : x.1*x.2 ≤ 9006/10000)
    (hb : 12758/100000 ≤ x.2) (hb' : x.2 ≤ 12759/100000) :
    OriginalParent (chartWorld x) ∧ AnalyticAt ℝ chartWorld x ∧
    AnalyticAt ℝ chartSource x ∧ AnalyticAt ℝ chartRead x ∧
    (∀ W : OriginalWorld, OriginalParent W → W.1 = x.1*x.2 → W.2.1 = x.2 →
      W = chartWorld x) ∧
    originalResponse (chartWorld x) = response (chartCoordinates x) ∧
    (chartWorld x).1/(chartWorld x).2.1 = x.1 := by
  have h0 : 0 < x.2 := by linarith
  have hr0 : 0 < x.1*x.2 := by linarith
  have hr1 : x.1*x.2 < 1 := by linarith
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity (x.1*x.2) x.2 hr0.le hr1.le h0
  have hl := ne_of_lt (strip_denominator _ _ hr hr' hb hb')
  have hworld := chart_analytic x (ne_of_gt h0) (ne_of_gt hj) (ne_of_gt hn)
    (ne_of_gt ht) (ne_of_gt hu) hl
  have wr : AnalyticAt ℝ (fun y => (chartWorld y).1) x := analyticAt_fst.comp hworld
  have wtail := analyticAt_snd.comp hworld
  have wb : AnalyticAt ℝ (fun y => (chartWorld y).2.1) x := analyticAt_fst.comp wtail
  have wtail' := analyticAt_snd.comp wtail
  have wd : AnalyticAt ℝ (fun y => (chartWorld y).2.2.1) x := analyticAt_fst.comp wtail'
  have wcoeff := analyticAt_snd.comp wtail'
  have wa (i : Fin 4) : AnalyticAt ℝ (fun y => (chartWorld y).2.2.2 i) x :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).analyticAt _).comp
      wcoeff
  have wa0 := wa 0
  have wa1 := wa 1
  have wa2 := wa 2
  have wa3 := wa 3
  refine ⟨encoded_parent _ (chart_parent x hr0 hr1 h0 hl),hworld,?_,?_,
    chart_unique x hl,encoded_response _,?_⟩
  · unfold chartSource sourceCoordinates
    apply AnalyticAt.pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
    all_goals fun_prop (disch := exact ne_of_gt h0)
  · unfold chartRead originalResponse originalRead originalPolynomial futureRead
    simp only [List.length_nil, Nat.cast_zero,add_zero]
    simp [originalPolynomial,Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,
      sourceMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
    fun_prop (disch := exact ne_of_gt h0)
  · dsimp [chartWorld,encodeWorld,parentWorld,chartCoordinates]
    exact mul_div_cancel_right₀ _ (ne_of_gt h0)

#print axioms analytic_original_parent_chart

end D5.S3.Observer.CubicGain.RegularParentChart
