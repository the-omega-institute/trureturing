/- GID: D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact fair unknown-coupling solution yields an unconditional nonfair-kernel global upper bound and an explicit feasible law within a certified one-sided deficit. -/

import D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorKernelStability

/-!
Only the two mediator marginals and all individual outcome-success means are
fixed. The mediator coupling and complete outcome law both range, independently,
in the original complete-mediation model. A fair anchor is constructed by the
existing exact partition theorem. No nonfair optimizer is a premise of the
principal enclosure theorem.

General shadow-coupling stability is established mathematics. Here the full
causal drift is retained and the upper fair-anchor envelope is sharpened: after
subtracting that drift, every nonfair value is bounded by the fair optimum,
without adding the transport radius. The lower endpoint is an actual feasible
model constructed using the same mediator coupling as the anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.NonfairMediationEnclosure

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.PartialMediatorTransportReduction
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.UnknownCouplingFairMediation
open D5.S3.ConceptDynamics.CausalMoments.BooleanOutcomeMarginalTransport
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorKernelStability

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The actual attainable values under a prescribed, possibly nonfair, kernel. -/
def kernelBenefitValues (control treated : FiniteResponseLaw M) (kernel : M → ℚ) : Set ℚ :=
  {value | ∃ coupling : FiniteResponseLaw (M × M), ∃ law : FiniteResponseLaw (M → Bool),
    HasMediatorMarginals coupling control treated ∧ (∀ i, tableMean law i = kernel i) ∧
      completeMediatorBenefit coupling law = value}

/-- Propagate a global upper bound between full kernel families by constructing
reverse transports. The original mediator coupling is retained in every case. -/
theorem transfer_kernel_upper_bound (control treated : FiniteResponseLaw M)
    (source target : M → ℚ) (source_mem : ∀ i, 0 ≤ source i ∧ source i ≤ 1)
    (bound : ℚ) (upper : ∀ value ∈ kernelBenefitValues control treated source, value ≤ bound) :
    ∀ value ∈ kernelBenefitValues control treated target,
      value ≤ bound+kernelDrift control treated source target+kernelRadius control treated source target := by
  rintro value ⟨coupling, law, marginals, means, rfl⟩
  obtain ⟨restored, restored_means, transported⟩ :=
    exists_uniform_kernel_transport control treated law source source_mem
  have h := transported coupling marginals
  have mean_eq : tableMean law = target := funext means
  rw [mean_eq, kernelDrift_swap, kernelRadius_swap] at h
  have bound_restored := upper (completeMediatorBenefit coupling restored)
    ⟨coupling, restored, marginals, restored_means, rfl⟩
  linarith [(abs_le.mp h).1]

/-- Whenever two actual attained optima are supplied, the full-family value
stability inequality follows; no missing optimizer existence is hidden here. -/
theorem attained_kernel_optima_stability (control treated : FiniteResponseLaw M)
    (source target : M → ℚ)
    (source_mem : ∀ i, 0 ≤ source i ∧ source i ≤ 1)
    (target_mem : ∀ i, 0 ≤ target i ∧ target i ≤ 1)
    (oldValue newValue : ℚ)
    (oldGreatest : IsGreatest (kernelBenefitValues control treated source) oldValue)
    (newGreatest : IsGreatest (kernelBenefitValues control treated target) newValue) :
    |newValue-oldValue-kernelDrift control treated source target| ≤
      kernelRadius control treated source target := by
  have forward := transfer_kernel_upper_bound control treated source target source_mem oldValue
    (fun _ h => oldGreatest.2 h) newValue newGreatest.1
  have reverse := transfer_kernel_upper_bound control treated target source target_mem newValue
    (fun _ h => newGreatest.2 h) oldValue oldGreatest.1
  rw [kernelDrift_swap, kernelRadius_swap] at reverse
  apply abs_le.mpr
  constructor <;> linarith

private theorem half_drift (control treated : FiniteResponseLaw M) (kernel : M → ℚ) :
    kernelDrift control treated (fun _ => 1/2) kernel =
      (∑ i, (treated.mass i-control.mass i)*kernel i)/2 := by
  have total : (∑ i, (treated.mass i - control.mass i)) = 0 := by
    rw [Finset.sum_sub_distrib, treated.total, control.total, sub_self]
  unfold kernelDrift
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, total, zero_mul, sub_zero]

/-- After removing the exact mean drift, the fair optimal partition already
bounds every nonfair model. There is no added uncertainty radius on this side. -/
theorem partition_anchor_upper (control treated : FiniteResponseLaw M)
    (best : M → Bool)
    (maximal : ∀ table, partitionScore control treated table ≤ partitionScore control treated best)
    (kernel : M → ℚ) (coupling : FiniteResponseLaw (M × M))
    (law : FiniteResponseLaw (M → Bool))
    (marginals : HasMediatorMarginals coupling control treated)
    (means : ∀ i, tableMean law i = kernel i) :
    completeMediatorBenefit coupling law ≤ partitionScore control treated best/2+
      kernelDrift control treated (fun _ => 1/2) kernel := by
  have cut_bound : linearObjective (mediatorCutMass coupling) law.mass ≤
      partitionScore control treated best := by
    calc
      _ ≤ ∑ table, partitionScore control treated best*law.mass table :=
        Finset.sum_le_sum (fun table _ => mul_le_mul_of_nonneg_right
          ((mediatorCutMass_le_partitionScore coupling control treated marginals table).trans
            (maximal table)) (law.nonnegative table))
      _ = _ := by rw [← Finset.mul_sum, law.total, mul_one]
  have identity := completeMediatorBenefit_mean_identity coupling control treated marginals law
  simp_rw [means] at identity
  rw [half_drift]
  linarith

/-- For every valid finite rational kernel, construct a real feasible pair of
independent mechanisms and a global upper bound. The two enclosing values are
separated by at most the transport radius, not twice that radius. -/
theorem nonfair_kernel_global_enclosure (control treated : FiniteResponseLaw M)
    (kernel : M → ℚ) (kernel_mem : ∀ i, 0 ≤ kernel i ∧ kernel i ≤ 1) :
    ∃ best : M → Bool,
      (∀ table, partitionScore control treated table ≤ partitionScore control treated best) ∧
      ∃ coupling : FiniteResponseLaw (M × M), ∃ law : FiniteResponseLaw (M → Bool),
        HasMediatorMarginals coupling control treated ∧
        (∀ i, tableMean law i = kernel i) ∧
        partitionScore control treated best/2+kernelDrift control treated (fun _ => 1/2) kernel-
          kernelRadius control treated (fun _ => 1/2) kernel ≤ completeMediatorBenefit coupling law ∧
        (∀ value ∈ kernelBenefitValues control treated kernel,
          value ≤ partitionScore control treated best/2+kernelDrift control treated (fun _ => 1/2) kernel) := by
  obtain ⟨best, maximal, interval⟩ := unknown_coupling_fair_interval control treated
  have nonnegative : 0 ≤ partitionScore control treated best/2 := by
    have h := maximal (fun _ => false)
    have zero : partitionScore control treated (fun _ => false) = 0 := by
      norm_num [partitionScore, partitionWeight, linearObjective]
    rw [zero] at h
    linarith
  obtain ⟨coupling, anchor, marginals, fair, value⟩ :=
    (interval (partitionScore control treated best/2)).mpr ⟨nonnegative, le_rfl⟩
  obtain ⟨law, means, transported⟩ :=
    exists_uniform_kernel_transport control treated anchor kernel kernel_mem
  have bound := transported coupling marginals
  have anchor_means : tableMean anchor = fun _ => 1/2 := funext fair
  rw [anchor_means, value] at bound
  refine ⟨best, maximal, coupling, law, marginals, means, ?_, ?_⟩
  · linarith [(abs_le.mp bound).1]
  · rintro v ⟨other, outcome, hm, hy, rfl⟩
    exact partition_anchor_upper control treated best maximal kernel other outcome hm hy

/-- Off-diagonal sensitivity weights are nonnegative and no greater than the
older sum-of-marginals weights. A forced self-pair strictly reduces the cost. -/
theorem sensitivityWeight_bounds (control treated : FiniteResponseLaw M) (i : M) :
    0 ≤ sensitivityWeight control treated i ∧
      sensitivityWeight control treated i ≤ control.mass i+treated.mass i := by
  have c1 : control.mass i ≤ 1 := by
    have h := Finset.single_le_sum (fun j _ => control.nonnegative j) (Finset.mem_univ i)
    rwa [control.total] at h
  have t1 : treated.mass i ≤ 1 := by
    have h := Finset.single_le_sum (fun j _ => treated.nonnegative j) (Finset.mem_univ i)
    rwa [treated.total] at h
  have magnitude : |control.mass i+treated.mass i-1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [control.nonnegative i, treated.nonnegative i]
  unfold sensitivityWeight
  constructor
  · linarith
  · linarith [neg_le_abs (control.mass i+treated.mass i-1)]

/-- A uniform coordinate error epsilon gives a radius at most epsilon, on the
entire original mediator family. No dimension multiplier is introduced. -/
theorem kernelRadius_le_uniform_error (control treated : FiniteResponseLaw M)
    (r s : M → ℚ) (epsilon : ℚ) (close : ∀ i, |s i-r i| ≤ epsilon) :
    kernelRadius control treated r s ≤ epsilon := by
  have h : (∑ i, sensitivityWeight control treated i*|s i-r i|) ≤
      ∑ i, (control.mass i+treated.mass i)*epsilon := by
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_right (sensitivityWeight_bounds control treated i).2 (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (close i) (add_nonneg (control.nonnegative i) (treated.nonnegative i)))
  rw [← Finset.sum_mul, Finset.sum_add_distrib, control.total, treated.total] at h
  unfold kernelRadius
  linarith

#print axioms nonfair_kernel_global_enclosure
#print axioms attained_kernel_optima_stability
#print axioms kernelRadius_le_uniform_error

end D5.S3.ConceptDynamics.CausalMoments.NonfairMediationEnclosure
