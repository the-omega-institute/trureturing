/- GID: D5/S3/Quantum/Fibers/PhaseConditioningVariation
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/PhaseConditioningVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive bottom margins control the two symmetry-sensitive phase differences. -/

import D5.S3.Quantum.Fibers.FiniteRectangleTransport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace D5.S3.Quantum.Fibers.PhaseConditioningVariation

open Set Filter Topology MeasureTheory
open D5.S3.Quantum.Fibers.FiniteRectangleTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

def bottom : Fin 4 → Fin 5 := ![0,1,3,4]
def mass (b : Base) (k : ℝ) (i : Fin 4) : ℝ := probability b k (bottom i)
def Q (b : Base) (k : ℝ) : ℝ :=
  b.1*b.2.1*(1-b.2.2-b.1-b.2.1)+2*b.1*b.2.1*k-(1-b.2.2)*k^2
def gap (b : Base) : Fin 2 → ℝ := ![b.1-b.2.1,b.1+b.2.1-(1-b.2.2)]
def leftMode : Fin 2 → Fin 5 := ![1,0]
def rightMode : Fin 2 → Fin 5 := ![3,4]
def phaseDifference (h : Vec) (i : Fin 2) : ℝ := h (leftMode i)-h (rightMode i)

private lemma mass_total (b : Base) (k : ℝ) : ∑ i, mass b k i = 1-b.2.2 := by
  simp [mass,bottom,probability,Fin.sum_univ_succ]; ring

private lemma information_sum (b : Base) (k : ℝ) :
    information b k = ∑ i, 1/mass b k i := by
  simp [information,mass,bottom,Fin.sum_univ_succ]; ring

private lemma information_positive (b : Base) (hb : ValidBase b) (k : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) : 0 < information b k := by
  have hp := (fiberProbability b k hb hk).positive
  have := hp 0; have := hp 1; have := hp 3; have := hp 4
  unfold information; positivity

private lemma q_identity (b : Base) (hb : ValidBase b) (k : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) :
    Q b k = information b k * ∏ i, mass b k i := by
  have hp := (fiberProbability b k hb hk).positive
  have hn (i : Fin 5) : probability b k i ≠ 0 := (hp i).ne'
  change Q b k = information b k *
    (probability b k 0*(probability b k 1*(probability b k 3*(probability b k 4*1))))
  unfold information
  field_simp [hn]
  · simp [Q,probability]; ring

/-- The denominator stays positive even when the lower endpoint is nonzero. -/
theorem denominator_margin (b : Base) (hb : ValidBase b) (k ε : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) (hε : 0 < ε)
    (hm : ∀ i, ε ≤ mass b k i) :
    Q b k = information b k * ∏ i, mass b k i ∧ 4*ε^3 ≤ Q b k ∧ 0 < Q b k := by
  have hp (i : Fin 4) : 0 < mass b k i := (fiberProbability b k hb hk).positive _
  have hs : information b k * ∏ i, mass b k i =
      mass b k 1*mass b k 2*mass b k 3+
      mass b k 0*mass b k 2*mass b k 3+
      mass b k 0*mass b k 1*mass b k 3+
      mass b k 0*mass b k 1*mass b k 2 := by
    rw [information_sum]
    norm_num only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.reduceFinMk, mul_one, add_zero]
    field_simp [(hp 0).ne', (hp 1).ne', (hp 2).ne', (hp 3).ne']
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
    ring
  have ht (i j l : Fin 4) : ε^3 ≤ mass b k i*mass b k j*mass b k l := by
    calc
      ε^3 = ε*ε*ε := by ring
      _ ≤ mass b k i*mass b k j*mass b k l :=
        mul_le_mul (mul_le_mul (hm i) (hm j) hε.le (hp i).le) (hm l) hε.le
          (mul_nonneg (hp i).le (hp j).le)
  have hid := q_identity b hb k hk
  refine ⟨hid,?_,?_⟩
  · rw [hid,hs]; linarith [ht 1 2 3,ht 0 2 3,ht 0 1 3,ht 0 1 2]
  · rw [hid]; exact mul_pos (information_positive b hb k hk)
      (Finset.prod_pos (fun i _ => hp i))

private lemma information_coercive (b : Base) (hb : ValidBase b) (k : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) : 16 ≤ information b k*(1-b.2.2) := by
  have hp (i : Fin 4) (_ : i ∈ (Finset.univ : Finset (Fin 4))) :
      0 < mass b k i := (fiberProbability b k hb hk).positive _
  have hs := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun _ : Fin 4 => (1:ℝ)) hp
  rw [mass_total] at hs
  norm_num only [one_pow] at hs
  rw [← information_sum] at hs
  norm_num at hs
  exact (div_le_iff₀ (by linarith [hb.2.1] : 0 < 1-b.2.2)).mp hs

private lemma reciprocal_difference (b : Base) (hb : ValidBase b) (k : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) (i : Fin 2) :
    phaseDifference (phaseWeight b k) i = gap b i /
      (information b k*probability b k (leftMode i)*probability b k (rightMode i)) := by
  have hp := (fiberProbability b k hb hk).positive
  have hI := (information_positive b hb k hk).ne'
  have hn (j : Fin 5) : probability b k j ≠ 0 := (hp j).ne'
  fin_cases i
  · change -1/(probability b k 1*information b k) - -1/(probability b k 3*information b k) =
      (b.1-b.2.1)/(information b k*probability b k 1*probability b k 3)
    field_simp [hI,hn]
    simp [probability] <;> ring
  · change 1/(probability b k 0*information b k) - 1/(probability b k 4*information b k) =
      (b.1+b.2.1-(1-b.2.2))/(information b k*probability b k 0*probability b k 4)
    field_simp [hI,hn]
    simp [probability] <;> ring

/-- Both symmetry gaps control the actual pointwise five-mode transport weights. -/
theorem pointwise_gap_bound (b : Base) (hb : ValidBase b) (k ε : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) (hε : 0 < ε)
    (hm : ∀ i, ε ≤ mass b k i) (i : Fin 2) :
    |phaseDifference (phaseWeight b k) i| ≤ |gap b i| *(1-b.2.2)/(16*ε^2) := by
  have hp := (fiberProbability b k hb hk).positive
  have hI := information_positive b hb k hk
  have hr : 0 < 1-b.2.2 := by linarith [hb.2.1]
  have hl : ε ≤ probability b k (leftMode i) := by
    fin_cases i
    · simpa [mass,bottom,leftMode] using hm 1
    · simpa [mass,bottom,leftMode] using hm 0
  have hright : ε ≤ probability b k (rightMode i) := by
    fin_cases i
    · simpa [mass,bottom,rightMode] using hm 2
    · simpa [mass,bottom,rightMode] using hm 3
  have hprod : ε^2 ≤ probability b k (leftMode i)*probability b k (rightMode i) := by
    simpa [pow_two] using mul_le_mul hl hright hε.le (hp _).le
  have hden : 0 < information b k*probability b k (leftMode i)*probability b k (rightMode i) :=
    mul_pos (mul_pos hI (hp _)) (hp _)
  have hcoerce := information_coercive b hb k hk
  have hbound : 16*ε^2 ≤
      (information b k*probability b k (leftMode i)*probability b k (rightMode i))*(1-b.2.2) := by
    calc
      16*ε^2 ≤ (information b k*(1-b.2.2))*ε^2 := mul_le_mul_of_nonneg_right hcoerce (sq_nonneg ε)
      _ ≤ (information b k*(1-b.2.2))*(probability b k (leftMode i)*probability b k (rightMode i)) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hI.le hr.le)
      _ = _ := by ring
  rw [reciprocal_difference b hb k hk i,abs_div,abs_of_pos hden]
  apply (div_le_div_iff₀ hden (by positivity : 0 < 16*ε^2)).mpr
  calc
    |gap b i| *(16*ε^2) ≤ |gap b i| *
        ((information b k*probability b k (leftMode i)*probability b k (rightMode i))*(1-b.2.2)) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = _ := by ring

/-- The estimate holds for the actual integral residual of any integrable phase rate. -/
theorem integral_variation_bound (b : Base) (hb : ValidBase b) (T ε : ℝ)
    (hT : 0 ≤ T) (hε : 0 < ε) (k α : ℝ → ℝ)
    (ha : IntervalIntegrable α volume 0 T)
    (hw : ∀ j, IntervalIntegrable (fun t => phaseWeight b (k t) j*α t) volume 0 T)
    (hk : ∀ t ∈ Icc (0:ℝ) T, k t ∈ Ioo (lower b) (upper b))
    (hm : ∀ t ∈ Icc (0:ℝ) T, ∀ j, ε ≤ mass b (k t) j) (i : Fin 2) :
    |phaseDifference (fun j => ∫ t in (0:ℝ)..T, phaseWeight b (k t) j*α t) i| ≤
      |gap b i| *(1-b.2.2)/(16*ε^2)*(∫ t in (0:ℝ)..T, |α t|) := by
  have he : phaseDifference (fun j => ∫ t in (0:ℝ)..T, phaseWeight b (k t) j*α t) i =
      ∫ t in (0:ℝ)..T, phaseDifference (phaseWeight b (k t)) i*α t := by
    unfold phaseDifference
    rw [← intervalIntegral.integral_sub (hw _) (hw _)]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [he,← intervalIntegral.integral_const_mul]
  apply (intervalIntegral.abs_integral_le_integral_abs hT).trans
  have hd : IntervalIntegrable (fun t => phaseDifference (phaseWeight b (k t)) i*α t) volume 0 T := by
    simpa only [phaseDifference,sub_mul] using (hw (leftMode i)).sub (hw (rightMode i))
  apply intervalIntegral.integral_mono_on hT hd.abs (ha.abs.const_mul _)
  intro t ht
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (pointwise_gap_bound b hb (k t) ε (hk t ht) hε (hm t ht) i)
    (abs_nonneg _)

#print axioms denominator_margin
#print axioms pointwise_gap_bound
#print axioms integral_variation_bound

end D5.S3.Quantum.Fibers.PhaseConditioningVariation
