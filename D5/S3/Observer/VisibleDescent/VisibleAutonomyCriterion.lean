/- GID: D5/S3/Observer/VisibleDescent/VisibleAutonomyCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/VisibleAutonomyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Visible descent, kernel inclusion, and zero hidden-to-visible flow are equivalent. -/

import D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-26):
   * `LinearDescentCriterion.linear_descent_criterion` is a bounded orthogonal
     Hilbert-space special case, while `LinearProjectionDescentCriterion` is a
     finite complex Hermitian-matrix special case. Neither is an exact owner for
     the source's arbitrary idempotent linear projection.
   * Searches for the three-clause shape involving descent on `range P`, kernel
     inclusion, and `P T (1 - P) = 0` found no D5 theorem at this generality.
   * Exact pinned-Mathlib hits `LinearMap.rangeRestrict`, `LinearMap.codRestrict`,
     and `List.TFAE` provide the canonical visible carrier and equivalence shell.
   * The frozen `visible_descent_does_not_prevent_hidden_leakage` supplies the
     source's one-sided countermodel and is applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.VisibleAutonomyCriterion

open D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria

universe u v

/-- For an idempotent linear projection, factorization of the next visible state
through the current visible range, inclusion of the projection kernel in the
next-visible kernel, and vanishing hidden-to-visible flow are equivalent.
The explicit two-coordinate example shows that this one-sided criterion does
not force the reverse cross block to vanish. -/
theorem visible_autonomy_criterion
    {R : Type u} {X : Type v} [Semiring R] [AddCommGroup X] [Module R X]
    (P T : Module.End R X) (idempotent : P.comp P = P) :
    let Q : Module.End R X := 1 - P
    let visible : X →ₗ[R] LinearMap.range P := P.rangeRestrict
    let visibleAfter : X →ₗ[R] LinearMap.range P :=
      (P.comp T).codRestrict (LinearMap.range P)
        (fun x => LinearMap.mem_range_self P (T x))
    List.TFAE [
      Exists fun descended : LinearMap.range P →ₗ[R] LinearMap.range P =>
        visibleAfter = descended.comp visible,
      LinearMap.ker P ≤ LinearMap.ker (P.comp T),
      (P.comp T).comp Q = 0] ∧
    (visibleCoordinateProjection.comp visibleCoordinateProjection =
          visibleCoordinateProjection ∧
      hiddenCoordinateProjection = 1 - visibleCoordinateProjection ∧
      (visibleCoordinateProjection.comp visibleToHiddenLeak).comp
          hiddenCoordinateProjection = 0 ∧
      (hiddenCoordinateProjection.comp visibleToHiddenLeak).comp
          visibleCoordinateProjection ≠ 0) := by
  let Q : Module.End R X := 1 - P
  let visible : X →ₗ[R] LinearMap.range P := P.rangeRestrict
  let visibleAfter : X →ₗ[R] LinearMap.range P :=
    (P.comp T).codRestrict (LinearMap.range P)
      (fun x => LinearMap.mem_range_self P (T x))
  change
    List.TFAE [
      Exists fun descended : LinearMap.range P →ₗ[R] LinearMap.range P =>
        visibleAfter = descended.comp visible,
      LinearMap.ker P ≤ LinearMap.ker (P.comp T),
      (P.comp T).comp Q = 0] ∧
    (visibleCoordinateProjection.comp visibleCoordinateProjection =
          visibleCoordinateProjection ∧
      hiddenCoordinateProjection = 1 - visibleCoordinateProjection ∧
      (visibleCoordinateProjection.comp visibleToHiddenLeak).comp
          hiddenCoordinateProjection = 0 ∧
      (hiddenCoordinateProjection.comp visibleToHiddenLeak).comp
          visibleCoordinateProjection ≠ 0)
  constructor
  · tfae_have 1 -> 2 := by
      rintro ⟨descended, commutes⟩ x xInKernel
      rw [LinearMap.mem_ker] at xInKernel ⊢
      have visibleZero : visible x = 0 := by
        apply Subtype.ext
        simpa [visible] using xInKernel
      have atX := LinearMap.congr_fun commutes x
      have valuesEqual := congrArg Subtype.val atX
      simpa [visibleAfter, LinearMap.comp_apply, visibleZero] using
        valuesEqual
    tfae_have 2 -> 3 := by
      intro kernelInclusion
      apply LinearMap.ext
      intro x
      have hiddenInKernel : Q x ∈ LinearMap.ker P := by
        rw [LinearMap.mem_ker]
        have idempotentAtX : P (P x) = P x :=
          LinearMap.congr_fun idempotent x
        simp [Q, idempotentAtX, Module.End.one_apply]
      have futureInKernel := kernelInclusion hiddenInKernel
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
        (LinearMap.mem_ker.mp futureInKernel)
    tfae_have 3 -> 1 := by
      intro crossBlock
      refine ⟨visibleAfter.domRestrict (LinearMap.range P), ?_⟩
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hiddenZero : P (T (Q x)) = 0 := by
        have atX := LinearMap.congr_fun crossBlock x
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using atX
      have decomposition : x = P x + Q x := by
        simp [Q, Module.End.one_apply]
      simp only [LinearMap.comp_apply, LinearMap.domRestrict_apply]
      dsimp only [visibleAfter, visible]
      change P (T x) = P (T (P x))
      calc
        P (T x) = P (T (P x + Q x)) := by rw [← decomposition]
        _ = P (T (P x)) + P (T (Q x)) := by simp
        _ = P (T (P x)) := by rw [hiddenZero, add_zero]
    tfae_finish
  · have crossBlocks := visible_descent_does_not_prevent_hidden_leakage
    refine ⟨?_, ?_, crossBlocks.1, crossBlocks.2⟩
    · apply LinearMap.ext
      intro x
      funext i
      fin_cases i <;> simp [visibleCoordinateProjection]
    · apply LinearMap.ext
      intro x
      funext i
      fin_cases i <;>
        simp [visibleCoordinateProjection, hiddenCoordinateProjection]

#print axioms visible_autonomy_criterion

end D5.S3.Observer.VisibleDescent.VisibleAutonomyCriterion
