/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth extension of the distinct-node tail and its repeated-node cancellation. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailFormula
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripProfile

/-! # The repeat-node tail correction as a finite exponential sum -/

open Finset Set

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

theorem leftStripCross_smooth (p : ℕ) :
    ContDiff ℝ 3 (Function.uncurry (leftStripCross p)) := by
  let h := 3/(p : ℝ)
  have hsum : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ tailSum p h z.1) := by
    unfold tailSum
    apply ContDiff.sum
    intro j _
    fun_prop
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ Real.exp (-((3+h)*(z.2-z.1))) *
    (1+h*upperTailGap h (z.2-z.1)*tailSum p h z.1))
  unfold upperTailGap
  fun_prop

theorem leftStripTailResidual_smooth (p : ℕ) :
    ContDiff ℝ 3 (Function.uncurry (leftStripTailResidual p)) := by
  let h := 3/(p : ℝ)
  have hc := leftStripCross_smooth p
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ leftStripCross p z.1 z.2) at hc
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦
    (upperTailRepeatCorrection h z.2+upperTailRepeatCorrection h (z.2-z.1))/2 -
      leftStripCross p z.1 z.2)
  unfold upperTailRepeatCorrection upperTailGap
  fun_prop

theorem mixed_partial_eq {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x,y)) :
    deriv (fun t ↦ deriv (f t) y) x = deriv (fun t ↦ deriv (f · t) x) y := by
  have h := Extreme.hasDerivAt_deriv_second hf
  exact h.deriv.trans (Extreme.hasDerivAt_deriv_first_of_second hf h).deriv.symm

#print axioms leftStripCross_eq

end RefinedBMV.PositiveCenter
