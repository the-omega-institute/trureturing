/- GID: D5/S3/Observer/CubicGain/RegularResponseCircuit
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/RegularResponseCircuit
   mirror-E: none(waiver:regular-original-response-circuit)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.FDeriv.Prod]
   utility: none
   digest: The regular polynomial circuit reconstructs the same whole original world and its actual fifth and eighth reads. -/

import D5.S3.Observer.CubicGain.RegularParentChart

/-! The integral response circuit and the original whole polynomial. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.RegularResponseCircuit

open D5.S3.Observer.CubicGain RegularParentChart CommonWordSensitivity

/-- Source traces in the independent `(t,b)` coordinates. -/
def circuitJ (x : ℝ × ℝ) : ℝ := x.1+x.2*(1-x.1^2)
def circuitN (x : ℝ × ℝ) : ℝ := circuitJ x+x.1*x.2

/-- The unexpanded integral denominator of the regular response circuit. -/
def circuitD (x : ℝ × ℝ) : ℝ :=
  5*((x.2^2+8*x.2+4)*circuitJ x*circuitN x-
    2*(1+x.2)*(1+2*x.2)*(circuitJ x+circuitN x))

def circuitA (x : ℝ × ℝ) : ℝ := (8*x.2-1)*(2+5*x.2)

/-- Numerators of the four samples of one whole gain, at nodes zero through three. -/
def circuitC (x : ℝ × ℝ) : Gain :=
  ![-24*circuitD x+3*circuitA x*circuitJ x*circuitN x,
    3*circuitA x*circuitN x,
    3*(49*x.2+34)*circuitJ x*circuitN x-
      54*(1+2*x.2)*(circuitJ x+circuitN x),
    3*circuitA x*circuitJ x]

def circuitP (x : ℝ × ℝ) : ℝ :=
  -circuitC x 0+(1+2*x.2+circuitN x)*
    (-4*circuitC x 0+15*circuitC x 1-20*circuitC x 2+10*circuitC x 3)

/-- The clock-eight M numerator uses the actual original whole gain. -/
def circuitM (x : ℝ × ℝ) : ℝ :=
  -circuitC x 0+(3+8*x.2+x.1*(1-x.1*x.2))*
    (-35*circuitC x 0+120*circuitC x 1-140*circuitC x 2+56*circuitC x 3)

private theorem circuit_traces (x : ℝ × ℝ) (hb : x.2 ≠ 0) :
    circuitJ x = sourceJ (x.1*x.2) x.2 ∧
    circuitN x = sourceN (x.1*x.2) x.2 := by
  dsimp [circuitJ,circuitN,sourceJ,sourceN]
  constructor <;> field_simp <;> ring

private theorem circuit_denominator (x : ℝ × ℝ)
    (hj : circuitJ x ≠ 0) (hn : circuitN x ≠ 0)
    (ht : 1+x.2 ≠ 0) (hu : 1+2*x.2 ≠ 0) :
    circuitD x = (5/2)*(1+x.2)*(1+2*x.2)*circuitJ x*circuitN x*
      (1+6/(1+x.2)+1/(1+2*x.2)-4/circuitJ x-4/circuitN x) := by
  unfold circuitD
  have hu' : 1+x.2*2 ≠ 0 := by simpa only [mul_comm] using hu
  field_simp [hj,hn,ht,hu,hu']
  <;> ring

/-- On every strict regular source, the integral circuit gives exactly the
same drift and all four samples as the original parent reconstruction.
No gain sample, coefficient or drift increment is assumed nonzero. -/
theorem regular_whole_gain_correspondence (x : ℝ × ℝ)
    (hr : 0 < x.1*x.2) (hr' : x.1*x.2 < 1) (hb : 0 < x.2)
    (hl : parentLambda (x.1*x.2) x.2 ≠ 0) :
    circuitD x ≠ 0 ∧
    -circuitC x 0/circuitD x = 24+regularError (x.1*x.2) x.2 ∧
    (fun i => circuitC x i/circuitD x) = parentGain (chartCoordinates x) := by
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity (x.1*x.2) x.2 hr.le hr'.le hb
  obtain ⟨ej,en⟩ := circuit_traces x (ne_of_gt hb)
  have hj' : circuitJ x ≠ 0 := by rw [ej]; exact ne_of_gt hj
  have hn' : circuitN x ≠ 0 := by rw [en]; exact ne_of_gt hn
  have hd : circuitD x = (5/2)*(1+x.2)*(1+2*x.2)*circuitJ x*circuitN x*
      parentLambda (x.1*x.2) x.2 := by
    rw [circuit_denominator x hj' hn' (ne_of_gt ht) (ne_of_gt hu)]
    rw [parentLambda,←ej,←en]
  have hpos : 0 < (5/2:ℝ)*(1+x.2)*(1+2*x.2)*circuitJ x*circuitN x := by
    rw [ej,en]
    positivity
  have hd0 : circuitD x ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (ne_of_gt hpos) hl
  have he : regularError (x.1*x.2) x.2 =
      -3*circuitA x*circuitJ x*circuitN x/circuitD x := by
    rw [hd]
    unfold regularError parentB circuitA
    field_simp [hl,hj',hn',ne_of_gt ht,ne_of_gt hu]
    <;> ring
  refine ⟨hd0,?_,?_⟩
  · rw [he]
    simp only [circuitC,Matrix.cons_val_zero]
    field_simp [hd0]
    <;> ring
  · ext i
    fin_cases i <;> simp only [circuitC,parentGain,chartCoordinates,
      Matrix.cons_val_zero',Matrix.cons_val_succ',he,←ej,←en]
    all_goals field_simp [hd0,hj',hn',ne_of_gt ht]
    all_goals try ring
    all_goals unfold circuitD circuitA
    all_goals ring

/-- Equality is in the original ordinary coefficient world, with the same
source matrix, drift and whole polynomial, rather than only in its reads. -/
theorem regular_world_correspondence (x : ℝ × ℝ)
    (hr : 0 < x.1*x.2) (hr' : x.1*x.2 < 1) (hb : 0 < x.2)
    (hl : parentLambda (x.1*x.2) x.2 ≠ 0) :
    chartWorld x = encodeWorld (x.1*x.2,x.2,-circuitC x 0/circuitD x,
      fun i => circuitC x i/circuitD x) := by
  obtain ⟨_,hd,hg⟩ := regular_whole_gain_correspondence x hr hr' hb hl
  dsimp [chartWorld,parentWorld,chartCoordinates]
  rw [hd,hg]
  rfl

/-- Both outputs are literal readings of that one original coefficient world. -/
theorem regular_actual_read_correspondence (x : ℝ × ℝ)
    (hr : 0 < x.1*x.2) (hr' : x.1*x.2 < 1) (hb : 0 < x.2)
    (hl : parentLambda (x.1*x.2) x.2 ≠ 0) :
    chartRead x = (circuitP x/circuitD x,circuitM x/circuitD x) := by
  obtain ⟨hd,_,_⟩ := regular_whole_gain_correspondence x hr hr' hb hl
  rw [chartRead,regular_world_correspondence x hr hr' hb hl]
  simp [originalResponse,originalRead,originalPolynomial,encodeWorld,gainCoefficients,
    Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,futureRead,
    List.length_nil,futureProduct,clockEight,chronological,sourceMatrix,actionJ,actionM,
    Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two,circuitP,circuitM,
    circuitN,circuitJ]
  constructor <;> field_simp <;> ring

#print axioms regular_whole_gain_correspondence
#print axioms regular_world_correspondence
#print axioms regular_actual_read_correspondence

end D5.S3.Observer.CubicGain.RegularResponseCircuit
