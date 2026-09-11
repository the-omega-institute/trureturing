/- GID: D5/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/CompleteMediatorKernelStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One exact outcome-marginal transport controls every compatible mediator coupling, with signed mean drift and marginal-only off-diagonal sensitivity weights. -/

import D5.S3.ConceptDynamics.CausalMoments.BooleanOutcomeMarginalTransport
import D5.S3.ConceptDynamics.CausalMoments.UnknownCouplingFairMediation

/-!
This consumes the original complete-mediation objective and two original
mediator marginals. Self-pairs have zero cut contribution. The weight
1-|alpha_i+beta_i-1| bounds the actual off-diagonal mass incident at i uniformly
over all compatible mediator couplings and can improve alpha_i+beta_i.

The outcome transport is constructed once, before quantifying over mediator
couplings. It changes no mediator law, and no joint-law convexification is used.
Additional outcome-table restrictions are not automatically preserved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorKernelStability

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.CausalMoments.PartialMediatorTransportReduction
open D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorCutSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.UnknownCouplingFairMediation
open D5.S3.ConceptDynamics.CausalMoments.BooleanOutcomeMarginalTransport

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Exact change of the mean-drift term in the original directed-cut identity. -/
def kernelDrift (control treated : FiniteResponseLaw M) (source target : M → ℚ) : ℚ :=
  (∑ i, (treated.mass i-control.mass i)*(target i-source i))/2

/-- Maximum off-diagonal incident mass allowed by the two original marginals. -/
def sensitivityWeight (control treated : FiniteResponseLaw M) (i : M) : ℚ :=
  1-|control.mass i+treated.mass i-1|

/-- Uniform radius; forced self-pair mass is excluded from the sensitivity cost. -/
def kernelRadius (control treated : FiniteResponseLaw M) (source target : M → ℚ) : ℚ :=
  (∑ i, sensitivityWeight control treated i * |target i-source i|)/2

/-- Swapping kernels reverses only the signed drift. -/
theorem kernelDrift_swap (control treated : FiniteResponseLaw M) (r s : M → ℚ) :
    kernelDrift control treated s r = -kernelDrift control treated r s := by
  unfold kernelDrift
  have h : (∑ i, (treated.mass i-control.mass i)*(r i-s i)) =
      -(∑ i, (treated.mass i-control.mass i)*(s i-r i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  ring

/-- The transport radius is symmetric. -/
theorem kernelRadius_swap (control treated : FiniteResponseLaw M) (r s : M → ℚ) :
    kernelRadius control treated s r = kernelRadius control treated r s := by
  unfold kernelRadius
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_sub_comm]

private def singletonTable (i : M) : M → Bool := fun j => decide (j=i)

private theorem singleton_score (control treated : FiniteResponseLaw M) (i : M) :
    partitionScore control treated (singletonTable i) = sensitivityWeight control treated i := by
  simp [partitionScore, partitionWeight, singletonTable, sensitivityWeight, linearObjective]

private theorem singleton_sum (pair : M × M) (change : M → ℚ) :
    (∑ i, (if singletonTable i pair.1 ≠ singletonTable i pair.2 then (1 : ℚ) else 0)*change i) =
      if pair.1=pair.2 then 0 else change pair.1+change pair.2 := by
  by_cases same : pair.1=pair.2
  · simp [same]
  · have point (i : M) :
        (if singletonTable i pair.1 ≠ singletonTable i pair.2 then (1 : ℚ) else 0)*change i =
          (if i=pair.1 then change i else 0)+(if i=pair.2 then change i else 0) := by
      by_cases first : i=pair.1 <;> by_cases second : i=pair.2 <;>
        simp_all [singletonTable, eq_comm]
    simp_rw [point, Finset.sum_add_distrib]
    simp [same]

private theorem weighted_singletons (coupling : FiniteResponseLaw (M × M)) (change : M → ℚ) :
    (∑ i, mediatorCutMass coupling (singletonTable i)*change i) =
      ∑ pair, (if pair.1=pair.2 then 0 else change pair.1+change pair.2)*coupling.mass pair := by
  calc
    _ = ∑ pair, (∑ i,
        (if singletonTable i pair.1 ≠ singletonTable i pair.2 then (1 : ℚ) else 0)*change i)*
          coupling.mass pair := by
      unfold mediatorCutMass linearObjective
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pair _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp_rw [singleton_sum]

private theorem abs_expectation_le {X : Type*} [Fintype X]
    (law : FiniteResponseLaw X) (f g : X → ℚ) (point : ∀ x, |f x| ≤ g x) :
    |linearObjective f law.mass| ≤ linearObjective g law.mass := by
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) =>
      mul_le_mul_of_nonneg_right (abs_le.mp (point x)).1 (law.nonnegative x))
    simpa only [linearObjective, neg_mul, Finset.sum_neg_distrib] using h
  · exact Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_right (abs_le.mp (point x)).2 (law.nonnegative x))

private theorem cut_point_bound (coupling : FiniteResponseLaw (M × M))
    (first second : M → Bool) :
    |mediatorCutMass coupling second-mediatorCutMass coupling first| ≤
      ∑ i, mediatorCutMass coupling (singletonTable i)*(if first i ≠ second i then 1 else 0) := by
  rw [weighted_singletons]
  have h := abs_expectation_le coupling
    (fun pair => (if second pair.1 ≠ second pair.2 then (1 : ℚ) else 0)-
      (if first pair.1 ≠ first pair.2 then 1 else 0))
    (fun pair => if pair.1=pair.2 then 0 else
      (if first pair.1 ≠ second pair.1 then (1 : ℚ) else 0)+
        (if first pair.2 ≠ second pair.2 then 1 else 0)) (by
      intro pair
      by_cases same : pair.1=pair.2
      · simp [same]
      · cases f0 : first pair.1 <;> cases f1 : first pair.2 <;>
          cases s0 : second pair.1 <;> cases s1 : second pair.2 <;>
          norm_num [same, f0, f1, s0, s1])
  simpa only [mediatorCutMass, linearObjective, sub_mul, Finset.sum_sub_distrib] using h

private theorem paired_cut_bound (coupling : FiniteResponseLaw (M × M))
    (joint : FiniteResponseLaw ((M → Bool) × (M → Bool))) :
    |linearObjective (fun pair => mediatorCutMass coupling pair.2-mediatorCutMass coupling pair.1)
      joint.mass| ≤
      ∑ i, mediatorCutMass coupling (singletonTable i)*
        linearObjective (fun pair => if pair.1 i ≠ pair.2 i then 1 else 0) joint.mass := by
  have h := abs_expectation_le joint _ _ (fun pair => cut_point_bound coupling pair.1 pair.2)
  have exchange :
      linearObjective (fun pair => ∑ i, mediatorCutMass coupling (singletonTable i)*
        (if pair.1 i ≠ pair.2 i then (1 : ℚ) else 0)) joint.mass =
      ∑ i, mediatorCutMass coupling (singletonTable i)*
        linearObjective (fun pair => if pair.1 i ≠ pair.2 i then 1 else 0) joint.mass := by
    unfold linearObjective
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pair _
    ring
  rwa [exchange] at h

/-- Full mean drift expressed in the original mediator marginals. -/
theorem completeMediatorBenefit_mean_identity
    (coupling : FiniteResponseLaw (M × M)) (control treated : FiniteResponseLaw M)
    (marginals : HasMediatorMarginals coupling control treated)
    (law : FiniteResponseLaw (M → Bool)) :
    2*completeMediatorBenefit coupling law =
      linearObjective (mediatorCutMass coupling) law.mass +
        ∑ i, (treated.mass i-control.mass i)*tableMean law i := by
  have drift : (∑ pair, coupling.mass pair*(tableMean law pair.2-tableMean law pair.1)) =
      ∑ i, (treated.mass i-control.mass i)*tableMean law i := by
    simp only [Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => coupling.mass (i,j)*tableMean law j)]
    simp_rw [← Finset.sum_mul]
    change (∑ j, rightResponseMarginal coupling.mass j*tableMean law j)-
      (∑ i, leftResponseMarginal coupling.mass i*tableMean law i) = _
    simp_rw [marginals.1, marginals.2]
    simp only [sub_mul, Finset.sum_sub_distrib]
  have h := completeMediatorBenefit_cut_identity coupling law
  change 2*completeMediatorBenefit coupling law =
    linearObjective (mediatorCutMass coupling) law.mass +
      ∑ pair, coupling.mass pair*(tableMean law pair.2-tableMean law pair.1) at h
  rwa [drift] at h

/-- Construct one new outcome law before quantifying over all compatible
mediator couplings. Original dependence and source independence are accounted
for through the actual joint old/new table law, not a desired error premise. -/
theorem exists_uniform_kernel_transport
    (control treated : FiniteResponseLaw M) (original : FiniteResponseLaw (M → Bool))
    (target : M → ℚ) (target_mem : ∀ i, 0 ≤ target i ∧ target i ≤ 1) :
    ∃ moved : FiniteResponseLaw (M → Bool),
      (∀ i, tableMean moved i = target i) ∧
      ∀ coupling : FiniteResponseLaw (M × M),
        HasMediatorMarginals coupling control treated →
        |completeMediatorBenefit coupling moved-completeMediatorBenefit coupling original-
          kernelDrift control treated (tableMean original) target| ≤
            kernelRadius control treated (tableMean original) target := by
  classical
  obtain ⟨joint, originalE, targetE, mismatch⟩ := exists_exact_marginal_transport original target target_mem
  let moved := pushforwardResponseLaw joint Prod.snd
  have movedE (f : (M → Bool) → ℚ) :
      linearObjective f moved.mass = linearObjective (fun pair => f pair.2) joint.mass :=
    pushforward_linearObjective joint Prod.snd f
  have means : ∀ i, tableMean moved i = target i := by
    intro i
    exact (movedE _).trans (targetE i)
  refine ⟨moved, means, ?_⟩
  intro coupling marginals
  have cut_bound := paired_cut_bound coupling joint
  have cut_difference :
      linearObjective (fun pair => mediatorCutMass coupling pair.2-mediatorCutMass coupling pair.1)
        joint.mass = linearObjective (mediatorCutMass coupling) moved.mass-
          linearObjective (mediatorCutMass coupling) original.mass := by
    rw [movedE, ← originalE (mediatorCutMass coupling)]
    simp only [linearObjective, sub_mul, Finset.sum_sub_distrib]
  rw [cut_difference] at cut_bound
  simp_rw [mismatch] at cut_bound
  have weights : (∑ i, mediatorCutMass coupling (singletonTable i)*|target i-tableMean original i|) ≤
      ∑ i, sensitivityWeight control treated i*|target i-tableMean original i| := by
    apply Finset.sum_le_sum
    intro i _
    have bound := mediatorCutMass_le_partitionScore coupling control treated marginals (singletonTable i)
    rw [singleton_score] at bound
    exact mul_le_mul_of_nonneg_right bound (abs_nonneg _)
  have c := cut_bound.trans weights
  have first := completeMediatorBenefit_mean_identity coupling control treated marginals original
  have second := completeMediatorBenefit_mean_identity coupling control treated marginals moved
  simp_rw [means] at second
  have delta : (∑ i, (treated.mass i-control.mass i)*target i)-
      (∑ i, (treated.mass i-control.mass i)*tableMean original i) =
        2*kernelDrift control treated (tableMean original) target := by
    unfold kernelDrift
    rw [← Finset.sum_sub_distrib]
    have point (i : M) : (treated.mass i-control.mass i)*target i-
        (treated.mass i-control.mass i)*tableMean original i =
          (treated.mass i-control.mass i)*(target i-tableMean original i) := by ring
    simp_rw [point]
    ring
  unfold kernelRadius
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp c).1, (abs_le.mp c).2]

#print axioms exists_uniform_kernel_transport

end D5.S3.ConceptDynamics.CausalMoments.CompleteMediatorKernelStability
