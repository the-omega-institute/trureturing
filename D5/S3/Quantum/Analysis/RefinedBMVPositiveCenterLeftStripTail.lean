/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth extension of the distinct-node tail and its repeated-node cancellation. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailFormula
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripProfile

/-! # The repeat-node tail correction as a finite exponential sum -/

open Finset

noncomputable section

namespace RefinedBMV.PositiveCenter

private def tailSum (p : ℕ) (h a : ℝ) : ℝ :=
  ∑ j ∈ range (p+1), Real.exp (-(h*((j : ℝ)+1)*a))

/-- The distinct-node correction extended smoothly through the lower
collision, with (a) and (v) as independent coordinates. -/
def leftStripCross (p : ℕ) (a v : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  let s := v-a
  Real.exp (-((3+h)*s)) * (1+h*upperTailGap h s*tailSum p h a)

private theorem gap_relation {h : ℝ} (hh : 0 < h) (t : ℝ) :
    h*upperTailGap h t = 1-Real.exp (-(h*t)) := by
  unfold upperTailGap
  field_simp [hh.ne']

/-- The smooth extension equals the original correction at distinct nodes. -/
theorem leftStripCross_eq {p : ℕ} (hp : 0 < p) {a v : ℝ} (ha : 0 < a) :
    let h := 3/(p : ℝ)
    leftStripCross p a v = upperTailCrossCorrection h a (v-a) := by
  let h := 3/(p : ℝ)
  let q := Real.exp (-(h*a))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hpH : h*(p : ℝ) = 3 := by dsimp [h]; field_simp [hpR.ne']
  have hgap : 0 < upperTailGap h a := by
    unfold upperTailGap
    exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ha)))) hh
  have hsum : 1+tailSum p h a = ∑ j ∈ range (p+2), q^j := by
    rw [Finset.sum_range_succ', pow_zero, add_comm 1]
    congr 1
    exact sum_congr rfl fun j _ ↦ by
      unfold q
      rw [← Real.exp_nat_mul]
      push_cast
      congr 1
      ring
  have hpow : q^(p+2) = Real.exp (-((3+2*h)*a)) := by
    unfold q
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    linear_combination -a*hpH
  have hgeom := geom_sum_mul_neg q (p+2)
  rw [← hsum, hpow, ← gap_relation hh a] at hgeom
  have hcoef : (1-Real.exp (-((3+2*h)*a)))/upperTailGap h a =
      h+h*tailSum p h a := by
    apply (div_eq_iff hgap.ne').2
    linear_combination -hgeom
  change _ = upperTailCrossCorrection h a (v-a)
  unfold upperTailCrossCorrection leftStripCross
  change _ = Real.exp (-((3+h)*(v-a))) *
    (Real.exp (-(h*(v-a))) + upperTailGap h (v-a) *
      (1-Real.exp (-((3+2*h)*a)))/upperTailGap h a)
  have hQ : Real.exp (-(h*(v-a))) = 1-h*upperTailGap h (v-a) := by
    linarith only [gap_relation hh (v-a)]
  rw [mul_div_assoc, hcoef, hQ]
  ring

/-- The unweighted tail residual that enters the lower-collision profile. -/
def leftStripTailResidual (p : ℕ) (a v : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  (upperTailRepeatCorrection h v + upperTailRepeatCorrection h (v-a))/2 -
    leftStripCross p a v

private theorem hasDerivAt_repeat {h t : ℝ} (hh : 0 < h) :
    HasDerivAt (upperTailRepeatCorrection h)
      (-((3+h)*(3+2*h))*upperTailGap h t*Real.exp (-((3+h)*t))) t := by
  let α := 3+h
  have he := (((hasDerivAt_id' t).const_mul α).neg).exp
  have hd := (((hasDerivAt_upperTailGap (t := t) hh).const_mul α).const_add 1).mul he
  change HasDerivAt (upperTailRepeatCorrection h) _ t at hd
  apply hd.congr_deriv
  dsimp [α]
  linear_combination (3+h)*Real.exp (-((3+h)*t))*(gap_relation hh t)

private theorem tailSum_zero (p : ℕ) (h : ℝ) : tailSum p h 0 = (p : ℝ)+1 := by
  simp [tailSum]

private theorem hasDerivAt_tailSum_zero (p : ℕ) (h : ℝ) :
    HasDerivAt (tailSum p h) (-h*((p : ℝ)+1)*((p : ℝ)+2)/2) 0 := by
  have hd (j : ℕ) : HasDerivAt (fun a : ℝ ↦ Real.exp (-(h*((j : ℝ)+1)*a)))
      (-h*((j : ℝ)+1)) 0 := by
    have he := (((hasDerivAt_id' (0 : ℝ)).const_mul (h*((j : ℝ)+1))).neg).exp
    convert he using 1 <;> simp [neg_mul]
  have hsum := HasDerivAt.fun_sum fun j (_ : j ∈ range (p+1)) ↦ hd j
  change HasDerivAt (tailSum p h) _ 0 at hsum
  apply hsum.congr_deriv
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  have hmoment : (∑ j ∈ range (p+1), (j : ℝ))*2 = ((p : ℝ)+1)*p := by
    have hm : (∑ j ∈ range (p+1), j)*2 = (p+1)*p := by
      simpa using sum_range_id_mul_two (p+1)
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) hm
  linear_combination (-h/2)*hmoment

/-- The smooth residual vanishes to second order at the repeated node. -/
theorem leftStripTailResidual_zero {p : ℕ} (hp : 0 < p) (v : ℝ) :
    leftStripTailResidual p 0 v = 0 ∧ HasDerivAt (leftStripTailResidual p · v) 0 0 := by
  let h := 3/(p : ℝ)
  let α := 3+h
  let β := 3+2*h
  let U := upperTailRepeatCorrection h
  let F := upperTailGap h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hpH : h*(p : ℝ) = 3 := by dsimp [h]; field_simp [hpR.ne']
  have hα : h*((p : ℝ)+1) = α := by dsimp [α]; linarith only [hpH]
  have hβ : h*((p : ℝ)+2) = β := by dsimp [β]; linarith only [hpH]
  have hcross : leftStripCross p 0 v = U v := by
    unfold leftStripCross U upperTailRepeatCorrection
    change Real.exp (-(α*(v-0))) * (1+h*F (v-0)*tailSum p h 0) = _
    rw [sub_zero, tailSum_zero]
    linear_combination (F v * Real.exp (-(α*v)))*hα
  constructor
  · change (U v+U (v-0))/2-leftStripCross p 0 v = 0
    rw [sub_zero, hcross]
    ring
  have hshift := (hasDerivAt_id' (0 : ℝ)).const_sub v
  have hU := (hasDerivAt_repeat (t := v-0) hh).comp 0 hshift
  have hF := (hasDerivAt_upperTailGap (t := v-0) hh).comp 0 hshift
  have he := (hshift.const_mul α).neg.exp
  have hd := he.mul (((hF.const_mul h).mul (hasDerivAt_tailSum_zero p h)).const_add 1)
  change HasDerivAt (leftStripCross p · v) _ 0 at hd
  have hcor := (((hU.const_add (U v)).div_const 2).sub hd)
  change HasDerivAt (leftStripTailResidual p · v) _ 0 at hcor
  apply hcor.congr_deriv
  let E := Real.exp (-(α*(v-0)))
  let Q := Real.exp (-(h*(v-0)))
  let m := tailSum p h 0
  change -(α*β)*F (v-0)*E*(-1)/2 -
    (E*(-(α*(-1)))*(1+h*F (v-0)*m) +
      E*(h*(Q*(-1))*m+h*F (v-0)*(-h*((p : ℝ)+1)*((p : ℝ)+2)/2))) = 0
  dsimp only [E, Q, m]
  rw [sub_zero, tailSum_zero]
  dsimp only [α, β] at hα hβ ⊢
  have hgap := gap_relation hh v
  -- The first moment of the finite sum makes the two derivatives identical.
  linear_combination
    (Real.exp (-((3+h)*v))*(Real.exp (-(h*v))-(3+h)*F v+h*((p : ℝ)+2)*F v/2))*hα +
    (Real.exp (-((3+h)*v))*(3+h)*F v/2)*hβ +
    (Real.exp (-((3+h)*v))*(3+h))*hgap

#print axioms leftStripCross_eq
#print axioms leftStripTailResidual_zero

end RefinedBMV.PositiveCenter
