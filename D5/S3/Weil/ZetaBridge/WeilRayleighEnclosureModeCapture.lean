/- GID: D5/S3/Weil/ZetaBridge/WeilRayleighEnclosureModeCapture
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilRayleighEnclosureModeCapture
   mirror-E: none(waiver:operator-domain-variational-bridge)
   anchors: []
   digest: Two-sided Rayleigh enclosure and codimension-one coercivity capture the ground line without an operator residual. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.Ring

/-!
# Rayleigh enclosure captures a ground line

The intended application is an unbounded self-adjoint operator.  `D` is its
linear operator domain, `ι : D -> H` is the domain embedding and `A : D -> H`
is the operator action.  Thus this file does not replace the arithmetic Weil
operator by an everywhere-defined bounded endomorphism.

Suppose a normalized candidate `k` has Rayleigh quotient at most `upper`, the
actual normalized ground eigenvector `u` has eigenvalue at least `lower`, and
every operator-domain vector orthogonal to `k` has energy at least `threshold`.
If `upper < threshold`, the orthogonal part of `u` is bounded by the width of
the two-sided Rayleigh enclosure:

  (threshold - upper) * ||u - <k,u> k||^2 <= upper - lower.

This is deliberately different from a Davis--Kahan residual estimate.  It
uses only quantities that a lower-form/Schur certificate can directly bound:
a candidate upper energy, a ground-energy lower bound and a codimension-one
coercivity threshold.  The theorem is stated over a real invariant domain.
For the arithmetic Weil application, passage from the conjugation-invariant
complex form to this real subspace is a separate operator/domain bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilRayleighEnclosureModeCapture

/-- A two-sided Rayleigh enclosure plus codimension-one coercivity bounds the
orthogonal mass of a normalized ground eigenvector.  The operator is allowed
to be unbounded: only its linear domain `D`, its embedding `ι`, and its action
`A : D -> H` enter the statement. -/
theorem rayleigh_enclosure_mode_capture
    {H D : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [AddCommGroup D] [Module ℝ D]
    (ι A : D →ₗ[ℝ] H) (k u : D)
    (lower upper threshold eigenvalue : ℝ)
    (symmetricOnDomain : ∀ x y : D,
      ⟪ι x, A y⟫_ℝ = ⟪A x, ι y⟫_ℝ)
    (candidateNormalized : ‖ι k‖ = 1)
    (groundNormalized : ‖ι u‖ = 1)
    (groundEigen : A u = eigenvalue • ι u)
    (groundLower : lower ≤ eigenvalue)
    (candidateAboveGround : eigenvalue ≤ ⟪ι k, A k⟫_ℝ)
    (candidateUpper : ⟪ι k, A k⟫_ℝ ≤ upper)
    (upperBelowThreshold : upper < threshold)
    (complementCoercive : ∀ f : D,
      ⟪ι k, ι f⟫_ℝ = 0 →
        threshold * ‖ι f‖ ^ 2 ≤ ⟪ι f, A f⟫_ℝ) :
    0 < threshold - upper ∧
      (threshold - upper) *
          ‖ι (u - ⟪ι k, ι u⟫_ℝ • k)‖ ^ 2 ≤ upper - lower := by
  let α : ℝ := ⟪ι k, ι u⟫_ℝ
  let v : D := u - α • k
  have imageV : ι v = ι u - α • ι k := by
    simp [v]
  have actionV : A v = A u - α • A k := by
    simp [v]
  have domainDecomposition : u = α • k + v := by
    simp [v]
  have imageDecomposition : ι u = α • ι k + ι v := by
    rw [domainDecomposition, map_add, map_smul]
  have actionDecomposition : A u = α • A k + A v := by
    rw [domainDecomposition, map_add, map_smul]
  have orthogonal : ⟪ι k, ι v⟫_ℝ = 0 := by
    rw [imageV, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, candidateNormalized]
    dsimp [α]
    ring
  have residualInnerGround : ⟪ι v, ι u⟫_ℝ = ‖ι v‖ ^ 2 := by
    rw [imageDecomposition, inner_add_right, real_inner_smul_right,
      real_inner_comm (ι v) (ι k), orthogonal, mul_zero, zero_add,
      real_inner_self_eq_norm_sq]
  have symmetricCross : ⟪ι k, A v⟫_ℝ = ⟪ι v, A k⟫_ℝ := by
    calc
      ⟪ι k, A v⟫_ℝ = ⟪A k, ι v⟫_ℝ := symmetricOnDomain k v
      _ = ⟪ι v, A k⟫_ℝ := real_inner_comm _ _
  have crossIdentity :
      ⟪ι v, A k⟫_ℝ =
        α * (eigenvalue - ⟪ι k, A k⟫_ℝ) := by
    have h := congrArg (fun z : H => ⟪ι k, z⟫_ℝ) groundEigen
    rw [actionDecomposition, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, symmetricCross] at h
    calc
      ⟪ι v, A k⟫_ℝ =
          eigenvalue * α - α * ⟪ι k, A k⟫_ℝ := by
            dsimp [α] at h ⊢
            linarith
      _ = α * (eigenvalue - ⟪ι k, A k⟫_ℝ) := by ring
  have residualEnergyIdentity :
      ⟪ι v, A v⟫_ℝ =
        eigenvalue * ‖ι v‖ ^ 2 +
          α ^ 2 * (⟪ι k, A k⟫_ℝ - eigenvalue) := by
    have h := congrArg (fun z : H => ⟪ι v, z⟫_ℝ) groundEigen
    rw [actionDecomposition, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, crossIdentity, residualInnerGround] at h
    calc
      ⟪ι v, A v⟫_ℝ =
          eigenvalue * ‖ι v‖ ^ 2 -
            α * (α * (eigenvalue - ⟪ι k, A k⟫_ℝ)) := by
              linarith
      _ = eigenvalue * ‖ι v‖ ^ 2 +
          α ^ 2 * (⟪ι k, A k⟫_ℝ - eigenvalue) := by ring
  have overlapSquareLeOne : α ^ 2 ≤ 1 := by
    have h := real_inner_mul_inner_self_le (ι k) (ι u)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      candidateNormalized, groundNormalized] at h
    simpa [α, pow_two] using h
  have rayleighExcessNonnegative :
      0 ≤ ⟪ι k, A k⟫_ℝ - eigenvalue :=
    sub_nonneg.mpr candidateAboveGround
  have overlapWeightedExcess :
      α ^ 2 * (⟪ι k, A k⟫_ℝ - eigenvalue) ≤
        ⟪ι k, A k⟫_ℝ - eigenvalue := by
    have h := mul_le_mul_of_nonneg_right overlapSquareLeOne
      rayleighExcessNonnegative
    simpa using h
  have coerciveV := complementCoercive v orthogonal
  rw [residualEnergyIdentity] at coerciveV
  have gapAgainstGround :
      (threshold - eigenvalue) * ‖ι v‖ ^ 2 ≤
        α ^ 2 * (⟪ι k, A k⟫_ℝ - eigenvalue) := by
    nlinarith [coerciveV]
  have eigenvalueBelowUpper : eigenvalue ≤ upper :=
    candidateAboveGround.trans candidateUpper
  have normSquareNonnegative : 0 ≤ ‖ι v‖ ^ 2 := sq_nonneg _
  have replaceGroundByUpper :
      (threshold - upper) * ‖ι v‖ ^ 2 ≤
        (threshold - eigenvalue) * ‖ι v‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right (by linarith) normSquareNonnegative
  have enclosureWidth :
      ⟪ι k, A k⟫_ℝ - eigenvalue ≤ upper - lower := by
    linarith
  have finalBound :
      (threshold - upper) * ‖ι v‖ ^ 2 ≤ upper - lower :=
    replaceGroundByUpper.trans
      (gapAgainstGround.trans (overlapWeightedExcess.trans enclosureWidth))
  constructor
  · linarith
  · simpa [v, α] using finalBound

#print axioms rayleigh_enclosure_mode_capture

end D5.S3.Weil.ZetaBridge.WeilRayleighEnclosureModeCapture
