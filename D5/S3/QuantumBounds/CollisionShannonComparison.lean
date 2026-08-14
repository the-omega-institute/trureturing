/- GID: D5/S3/QuantumBounds/CollisionShannonComparison
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/CollisionShannonComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Export the collision--Shannon bound and characterize equality on positive support. -/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import D5.S3.Entropy.MaxEntropy

/-!
# Collision entropy versus Shannon entropy

For a finite nonnegative law of total mass one, the negative logarithm of the squared-mass
sum is at most its Shannon entropy. The proof exports the positive-part substitution and
weighted logarithmic Jensen argument that was previously local to
`CollisionEntropyUncertainty.collision_entropy_uncertainty`.

Equality means that all positive masses are equal, i.e. the law is uniform on its support.
Full uniformity on the entire index type is sufficient but not necessary when zeros are allowed:
a point mass makes both sides zero. Thus no full-uniformity `iff` is claimed without an
everywhere-positive hypothesis. Normalization itself rules out an empty index type, so the
statements need no `[Nonempty ι]` hypothesis and the proofs do not synthesize one.

Pinned-mathlib search found the concave equality tools
`StrictConcaveOn.map_sum_eq_iff_of_pos`,
`StrictConcaveOn.map_sum_eq_iff_of_nonneg`, `StrictConcaveOn.map_sum_eq_iff`, and
`StrictConcaveOn.map_sum_eq_iff'` in `Mathlib/Analysis/Convex/Jensen.lean`.
`Real.negMulLog` is defined in `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`.
No `Real.inner_le_nnorm_mul_nnorm` declaration was found; nearby actual names are
`norm_inner_le_norm`, `nnnorm_inner_le_nnnorm`, and `real_inner_le_norm`.
No collision-entropy or Renyi-entropy declaration was found in pinned mathlib. Repository
search found finite Renyi divergence declarations, but no Renyi entropy and no exported
collision--Shannon comparison; the only match was the local proof step named above.

This module treats only the order-two collision expression; it does not state general
Renyi-entropy monotonicity.
-/

namespace D5.S3.QuantumBounds.CollisionShannonComparison

open D5.S3.Entropy.MaxEntropy

/-- The order-two collision entropy of a finite probability law is at most its Shannon entropy. -/
theorem collision_entropy_le_shannon_entropy {ι : Type*} [Fintype ι]
    (p : ι -> Real) (hp : (forall i, 0 <= p i) /\ ∑ i, p i = 1) :
    -Real.log (∑ i, (p i) ^ 2) <= shannonEntropy p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  classical
  let positivePart : ι -> Real := fun i => if p i = 0 then 1 else p i
  have hpositivePart (i : ι) : 0 < positivePart i := by
    by_cases hi : p i = 0
    · simp [positivePart, hi]
    · simp only [positivePart, hi, if_false]
      exact lt_of_le_of_ne (hp.1 i) (Ne.symm hi)
  have haverage : ∑ i, p i * positivePart i = ∑ i, (p i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i = 0
    · simp [positivePart, hi]
    · simp [positivePart, hi, pow_two]
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := p) (p := positivePart)
    (fun i _ => hp.1 i) (by simpa using hp.2)
    (fun i _ => hpositivePart i)
  simp only [smul_eq_mul] at hjensen
  rw [haverage] at hjensen
  rw [shannonEntropy]
  calc
    -Real.log (∑ i, (p i) ^ 2) <=
        -(∑ i, p i * Real.log (positivePart i)) := neg_le_neg hjensen
    _ = ∑ i, Real.negMulLog (p i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : p i = 0
      · simp [positivePart, hi]
      · simp [positivePart, hi, Real.negMulLog]

/-- Equality holds exactly when the law is uniform on its positive support. -/
theorem collision_entropy_eq_shannon_entropy_iff_uniform_on_support
    {ι : Type*} [Fintype ι] (p : ι -> Real)
    (hp : (forall i, 0 <= p i) /\ ∑ i, p i = 1) :
    -Real.log (∑ i, (p i) ^ 2) = shannonEntropy p <->
      forall i j, 0 < p i -> 0 < p j -> p i = p j := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  classical
  let positivePart : ι -> Real := fun i => if p i = 0 then 1 else p i
  have hpositivePart (i : ι) : 0 < positivePart i := by
    by_cases hi : p i = 0
    · simp [positivePart, hi]
    · simp only [positivePart, hi, if_false]
      exact lt_of_le_of_ne (hp.1 i) (Ne.symm hi)
  have haverage : ∑ i, p i * positivePart i = ∑ i, (p i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i = 0
    · simp [positivePart, hi]
    · simp [positivePart, hi, pow_two]
  have hentropy :
      shannonEntropy p = -(∑ i, p i * Real.log (positivePart i)) := by
    rw [shannonEntropy, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i = 0
    · simp [positivePart, hi]
    · simp [positivePart, hi, Real.negMulLog]
  have hjensen :
      Real.log (∑ i, p i * positivePart i) =
          ∑ i, p i * Real.log (positivePart i) <->
        forall ⦃j⦄, p j ≠ 0 -> forall ⦃k⦄, p k ≠ 0 ->
          positivePart j = positivePart k := by
    simpa only [Finset.mem_univ, true_implies, smul_eq_mul] using
      (strictConcaveOn_log_Ioi.map_sum_eq_iff_of_nonneg
        (t := Finset.univ) (w := p) (p := positivePart)
        (fun i _ => hp.1 i) (by simpa using hp.2)
        (fun i _ => hpositivePart i))
  rw [haverage] at hjensen
  constructor
  · intro heq i j hi hj
    have hlogeq :
        Real.log (∑ k, (p k) ^ 2) =
          ∑ k, p k * Real.log (positivePart k) := by
      rw [hentropy] at heq
      exact neg_inj.mp heq
    have hparts := (hjensen.mp hlogeq) (j := i) (ne_of_gt hi)
      (k := j) (ne_of_gt hj)
    simpa [positivePart, ne_of_gt hi, ne_of_gt hj] using hparts
  · intro huniform
    have hparts :
        forall ⦃j⦄, p j ≠ 0 -> forall ⦃k⦄, p k ≠ 0 ->
          positivePart j = positivePart k := by
      intro i hi j hj
      have hipos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hi)
      have hjpos : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hj)
      simpa [positivePart, hi, hj] using huniform i j hipos hjpos
    have hlogeq := hjensen.mpr hparts
    rw [hentropy]
    exact neg_inj.mpr hlogeq

/-- A law uniform on the entire index type attains the collision--Shannon equality. -/
theorem collision_entropy_eq_shannon_entropy_of_uniform
    {ι : Type*} [Fintype ι] (p : ι -> Real)
    (hp : (forall i, 0 <= p i) /\ ∑ i, p i = 1)
    (huniform : forall i j, p i = p j) :
    -Real.log (∑ i, (p i) ^ 2) = shannonEntropy p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  apply (collision_entropy_eq_shannon_entropy_iff_uniform_on_support p hp).2
  intro i j _ _
  exact huniform i j

#print axioms collision_entropy_le_shannon_entropy
#print axioms collision_entropy_eq_shannon_entropy_iff_uniform_on_support
#print axioms collision_entropy_eq_shannon_entropy_of_uniform

end D5.S3.QuantumBounds.CollisionShannonComparison
