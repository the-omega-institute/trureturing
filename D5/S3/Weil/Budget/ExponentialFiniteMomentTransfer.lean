/- GID: D5/S3/Weil/Budget/ExponentialFiniteMomentTransfer
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/ExponentialFiniteMomentTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exponentially bounded Cayley coefficients give a certified finite-moment tail. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/- Library-search audit trail (2026-08-29):
   * Repository searches for exponential finite-moment transfer, Cayley moment tails,
     Cauchy coefficient bounds, and the displayed geometric remainder found no exact D5 owner.
   * Body-shape searches for a `HasSum` moment transfer with uniform moment and geometric
     coefficient bounds found no canonical D5 declaration or definition to reuse.
   * Pinned Mathlib supplies `Summable.sum_add_tsum_nat_add`,
     `norm_tsum_le_tsum_norm`, and the real geometric-series lemmas used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Weil.Budget.ExponentialFiniteMomentTransfer

set_option maxHeartbeats 800000 in
-- Normalizing the two nested geometric tails exceeds the repository default.
/-- A complete Cayley moment transfer with the source Cauchy estimate has the stated
exponential finite-depth error. The coefficient and moment sequences remain the supplied
source data; the displayed envelope is constructed from the scale parameters. -/
theorem exponential_finite_moment_transfer
    (n M : Nat)
    (r rho radius : Real) (rhoLower : 1 < rho) (rhoUpper : rho < |r|⁻¹)
    (sourceMoment coefficient : Nat -> Complex) (targetMoment : Complex)
    (momentBound : forall k, ‖sourceMoment k‖ <= radius)
    (coefficientBound : forall k,
      ‖coefficient k‖ <=
        ((1 + |r|) ^ 2 * rho * (rho + |r|) ^ (n - 1) /
            (1 - |r| * rho) ^ (n + 1)) * rho⁻¹ ^ k)
    (transfer : HasSum (fun k => coefficient k * sourceMoment k) targetMoment) :
    ‖targetMoment - ∑ k ∈ Finset.range (M + 1), coefficient k * sourceMoment k‖ <=
      radius *
        ((1 + |r|) ^ 2 * rho * (rho + |r|) ^ (n - 1) /
          (1 - |r| * rho) ^ (n + 1)) *
        rho⁻¹ ^ (M + 1) / (1 - rho⁻¹) := by
  let envelope : Real :=
    (1 + |r|) ^ 2 * rho * (rho + |r|) ^ (n - 1) /
      (1 - |r| * rho) ^ (n + 1)
  let term : Nat -> Complex := fun k => coefficient k * sourceMoment k
  have rhoPositive : 0 < rho := lt_trans zero_lt_one rhoLower
  have rNonzero : r ≠ 0 := by
    intro rZero
    simp only [rZero, abs_zero, inv_zero] at rhoUpper
    exact (not_lt_of_ge rhoPositive.le) rhoUpper
  have absRPositive : 0 < |r| := abs_pos.mpr rNonzero
  have absRMulRho : |r| * rho < 1 := by
    calc
      |r| * rho < |r| * |r|⁻¹ :=
        mul_lt_mul_of_pos_left rhoUpper absRPositive
      _ = 1 := mul_inv_cancel₀ (ne_of_gt absRPositive)
  have ratioNonnegative : 0 <= rho⁻¹ := inv_nonneg.mpr rhoPositive.le
  have ratioLessOne : rho⁻¹ < 1 := inv_lt_one_of_one_lt₀ rhoLower
  have denominatorPositive : 0 < 1 - |r| * rho := sub_pos.mpr absRMulRho
  have envelopeNonnegative : 0 <= envelope := by
    dsimp [envelope]
    positivity
  have radiusNonnegative : 0 <= radius :=
    (norm_nonneg (sourceMoment 0)).trans (momentBound 0)
  have termBound : forall k, ‖term k‖ <= radius * envelope * rho⁻¹ ^ k := by
    intro k
    calc
      ‖term k‖ = ‖coefficient k‖ * ‖sourceMoment k‖ := norm_mul _ _
      _ <= (envelope * rho⁻¹ ^ k) * radius := by
        gcongr
        · simpa only [envelope] using coefficientBound k
        · exact momentBound k
      _ = radius * envelope * rho⁻¹ ^ k := by ring
  have geometricSummable : Summable (fun k : Nat => radius * envelope * rho⁻¹ ^ k) :=
    (summable_geometric_of_lt_one ratioNonnegative ratioLessOne).mul_left
      (radius * envelope)
  have normTermSummable : Summable (fun k => ‖term k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg (term k)) termBound geometricSummable
  have termSummable : Summable term := normTermSummable.of_norm
  have decomposition := termSummable.sum_add_tsum_nat_add (M + 1)
  have tailIdentity :
      targetMoment - ∑ k ∈ Finset.range (M + 1), term k =
        ∑' k : Nat, term (k + (M + 1)) := by
    rw [transfer.tsum_eq] at decomposition
    rw [← decomposition]
    abel
  have tailNormSummable : Summable (fun k : Nat => ‖term (k + (M + 1))‖) :=
    (summable_nat_add_iff (M + 1)).mpr normTermSummable
  have tailGeometricSummable :
      Summable (fun k : Nat => radius * envelope * rho⁻¹ ^ (k + (M + 1))) :=
    (summable_nat_add_iff (M + 1)).mpr geometricSummable
  rw [tailIdentity]
  calc
    ‖∑' k : Nat, term (k + (M + 1))‖ <=
        ∑' k : Nat, ‖term (k + (M + 1))‖ :=
      norm_tsum_le_tsum_norm tailNormSummable
    _ <= ∑' k : Nat, radius * envelope * rho⁻¹ ^ (k + (M + 1)) :=
      tailNormSummable.tsum_le_tsum
        (fun k => termBound (k + (M + 1))) tailGeometricSummable
    _ = radius * envelope * rho⁻¹ ^ (M + 1) / (1 - rho⁻¹) := by
      calc
        (∑' k : Nat, radius * envelope * rho⁻¹ ^ (k + (M + 1))) =
            ∑' k : Nat, (radius * envelope * rho⁻¹ ^ (M + 1)) * rho⁻¹ ^ k := by
          congr 1
          funext k
          rw [pow_add]
          ring
        _ = radius * envelope * rho⁻¹ ^ (M + 1) * (1 - rho⁻¹)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one ratioNonnegative ratioLessOne]
        _ = radius * envelope * rho⁻¹ ^ (M + 1) / (1 - rho⁻¹) := by
          rw [div_eq_mul_inv]
    _ = radius *
        ((1 + |r|) ^ 2 * rho * (rho + |r|) ^ (n - 1) /
          (1 - |r| * rho) ^ (n + 1)) *
        rho⁻¹ ^ (M + 1) / (1 - rho⁻¹) := by
      rfl

#print axioms exponential_finite_moment_transfer

end D5.S3.Weil.Budget.ExponentialFiniteMomentTransfer
