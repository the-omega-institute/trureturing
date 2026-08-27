/- GID: D5/S3/Observer/Linear/GramianBehaviorQuotientMetric
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GramianBehaviorQuotientMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify Gramian zero distance with equality of all future readouts. -/

import D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity

/- Library-search audit trail (2026-08-27):
   * The exact family primitives `observedIterate`, `discountedGramianTerm`, and
     `discountedObservabilityGramian` are imported rather than redeclared.
   * `discounted_gramian_term_summable` supplies norm convergence. The related
     frozen `discounted_observability_gramian_kernel` states operator-kernel
     equality but does not expose the quadratic zero-distance clause here.
   * Pinned Mathlib searches found no packaged observability-Gramian quotient
     metric theorem. Infinite-sum transport and `Summable.tsum_pos` provide the
     exact nonnegative-energy argument below.
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.GramianBehaviorQuotientMetric

open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder
open D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity

private theorem discounted_gramian_term_energy
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (beta : Real) (n : Nat) (x : V) :
    RCLike.re (inner K x (discountedGramianTerm T C beta n x)) =
      beta ^ n * ‖observedIterate T C n x‖ ^ 2 := by
  letI := FiniteDimensional.complete K V
  letI := FiniteDimensional.complete K Y
  rw [discountedGramianTerm]
  simp only [smul_apply, inner_smul_right, RCLike.mul_re, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, sub_zero]
  rw [<- ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]

private theorem discounted_gramian_energy_summable
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (beta : Real)
    (betaPositive : 0 < beta)
    (convergent : Real.sqrt beta * ‖T.toContinuousLinearMap‖ < 1)
    (x : V) :
    Summable (fun n : Nat => beta ^ n * ‖observedIterate T C n x‖ ^ 2) := by
  letI := FiniteDimensional.complete K V
  letI := FiniteDimensional.complete K Y
  have termSummable :=
    discounted_gramian_term_summable T C beta betaPositive convergent
  have applied := termSummable.mapL ((ContinuousLinearMap.apply K V) x)
  have paired := applied.mapL (innerSL K x)
  have realPart := paired.mapL RCLike.reCLM
  change Summable (fun n : Nat =>
    RCLike.re (inner K x (discountedGramianTerm T C beta n x))) at realPart
  simpa only [discounted_gramian_term_energy] using realPart

private theorem discounted_gramian_quadratic_eq_energy
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (beta : Real)
    (betaPositive : 0 < beta)
    (convergent : Real.sqrt beta * ‖T.toContinuousLinearMap‖ < 1)
    (x : V) :
    RCLike.re (inner K x (discountedObservabilityGramian T C beta x)) =
      ∑' n : Nat, beta ^ n * ‖observedIterate T C n x‖ ^ 2 := by
  letI := FiniteDimensional.complete K V
  letI := FiniteDimensional.complete K Y
  have termSummable :=
    discounted_gramian_term_summable T C beta betaPositive convergent
  rw [discountedObservabilityGramian]
  change RCLike.re (inner K x (((ContinuousLinearMap.apply K V) x)
    (∑' n : Nat, discountedGramianTerm T C beta n))) = _
  rw [((ContinuousLinearMap.apply K V) x).map_tsum termSummable]
  have applied := termSummable.mapL ((ContinuousLinearMap.apply K V) x)
  change RCLike.re ((innerSL K x)
    (∑' n : Nat, ((ContinuousLinearMap.apply K V) x)
      (discountedGramianTerm T C beta n))) = _
  rw [(innerSL K x).map_tsum applied]
  have paired := applied.mapL (innerSL K x)
  change RCLike.reCLM
    (∑' n : Nat, (innerSL K x) (((ContinuousLinearMap.apply K V) x)
      (discountedGramianTerm T C beta n))) = _
  rw [RCLike.reCLM.map_tsum paired]
  congr 1
  funext n
  exact discounted_gramian_term_energy T C beta n x

/-- The Gramian quadratic form is the metric shadow of the quotient by complete
future-readout behavior: it vanishes on a pair exactly when every future
readout agrees on that pair. -/
theorem gramian_behavior_quotient_metric
    {K V Y : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (beta : Real)
    (discountRange : beta ∈ Set.Ioo 0 1)
    (convergent : Real.sqrt beta * ‖T.toContinuousLinearMap‖ < 1)
    (x y : V) :
    (forall n : Nat, C ((T ^ n) x) = C ((T ^ n) y)) <->
      RCLike.re (inner K (x - y)
        (discountedObservabilityGramian T C beta (x - y))) = 0 := by
  have energyIdentity := discounted_gramian_quadratic_eq_energy
    T C beta discountRange.1 convergent (x - y)
  have energySummable := discounted_gramian_energy_summable
    T C beta discountRange.1 convergent (x - y)
  constructor
  · intro sameBehavior
    rw [energyIdentity]
    calc
      (∑' n : Nat, beta ^ n * ‖observedIterate T C n (x - y)‖ ^ 2) =
          ∑' _n : Nat, (0 : Real) := by
        apply tsum_congr
        intro n
        have observedZero : observedIterate T C n (x - y) = 0 := by
          change C ((T ^ n) (x - y)) = 0
          rw [map_sub, map_sub, sameBehavior n, sub_self]
        simp [observedZero]
      _ = 0 := tsum_zero
  · intro zeroDistance n
    have totalZero :
        (∑' k : Nat, beta ^ k * ‖observedIterate T C k (x - y)‖ ^ 2) = 0 := by
      rw [<- energyIdentity, zeroDistance]
    apply sub_eq_zero.mp
    rw [<- map_sub, <- map_sub]
    by_contra observedNonzero
    have observedIterateNonzero : observedIterate T C n (x - y) ≠ 0 := by
      simpa [observedIterate, LinearMap.comp_apply, Module.End.coe_pow] using
        observedNonzero
    have positiveTerm :
        0 < beta ^ n * ‖observedIterate T C n (x - y)‖ ^ 2 :=
      mul_pos (pow_pos discountRange.1 n)
        (sq_pos_of_pos (norm_pos_iff.mpr observedIterateNonzero))
    have totalPositive :
        0 < ∑' k : Nat, beta ^ k * ‖observedIterate T C k (x - y)‖ ^ 2 :=
      energySummable.tsum_pos
        (fun k => mul_nonneg (pow_nonneg discountRange.1.le k) (sq_nonneg _))
        n positiveTerm
    exact totalPositive.ne totalZero.symm

#print axioms gramian_behavior_quotient_metric

end D5.S3.Observer.Linear.GramianBehaviorQuotientMetric
