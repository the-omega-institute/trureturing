/- GID: D5/S3/Combinatorics/PatternMatchings/P13Enumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Enumeration
   mirror-E: none(waiver:all-size-formal-coefficient-enumeration)
   anchors: []
   utility: none
   digest: Enumerates the original P13 avoiding perfect matchings at every size by an explicit formal coefficient formula. -/

import D5.S3.Combinatorics.PatternMatchings.P13HCoefficients
import D5.S3.Combinatorics.Nonnesting.CatalanLagrangeBridge
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

open PowerSeries
open scoped PowerSeries.WithPiTopology

local instance : UniformSpace ℚ := ⊥

noncomputable section

section BoundaryAlgebra

local notation "q" => (PowerSeries.X : PowerSeries ℚ)
local notation "C" => (1 + q)
local notation "δ" => ((1 - q) ^ 2)

private theorem boundary_algebra
    (A h0 h1 h2 P R T : PowerSeries ℚ)
    (e0 : q * h0 = C * (A - 1))
    (e1 : q ^ 2 * h1 + (δ - 2 * q) * h0 = C ^ 2 - 4 * q * A)
    (e2 : q ^ 3 * h2 + (δ - 2 * q ^ 2) * h1 + q * (1 - q) * h0 = 0)
    (eTail : δ * R * h2 + q ^ 2 * T * h1 = 0)
    (eScalar : δ ^ 2 * P = δ * (δ - 2 * q ^ 2) * R - q ^ 5 * T) :
    (A - 1) * (δ * (1 - 2 * q - q ^ 2) * P - q ^ 3 * (1 + q) * R) =
      q * (1 - q) ^ 3 * P := by
  have hC : IsUnit C :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
  have hs : IsUnit (1 - q) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
  have hδ : IsUnit δ := hs.pow 2
  -- Eliminate h2 with the tail and scalar contracts; cancel only the unit δ.
  have hElim : δ * P * h1 + q * (1 - q) * R * h0 = 0 := by
    apply hδ.mul_left_cancel
    linear_combination δ * R * e2 - q ^ 3 * eTail + h1 * eScalar
  -- Clear C in the first two coefficient equations without dividing by q.
  have hLow : C * q ^ 2 * h1 + (1 - q) * (1 - 2 * q - q ^ 2) * h0 = C * δ := by
    linear_combination C * e1 + 4 * q * e0
  -- This is (1-q) * D * h0 = C * δ^2 * P, with D expanded literally.
  have hBoundary :
      (1 - q) * (δ * (1 - 2 * q - q ^ 2) * P - q ^ 3 * (1 + q) * R) * h0 =
        C * δ ^ 2 * P := by
    linear_combination δ * P * hLow - C * q ^ 2 * hElim
  -- Multiply the boundary identity by q, use e0, then cancel C and 1-q.
  apply hs.mul_left_cancel
  apply hC.mul_left_cancel
  calc
    C * ((1 - q) * ((A - 1) *
        (δ * (1 - 2 * q - q ^ 2) * P - q ^ 3 * (1 + q) * R))) =
        q * ((1 - q) *
          (δ * (1 - 2 * q - q ^ 2) * P - q ^ 3 * (1 + q) * R) * h0) := by
      calc
        _ = (1 - q) *
            (δ * (1 - 2 * q - q ^ 2) * P - q ^ 3 * (1 + q) * R) *
              (C * (A - 1)) := by ring
        _ = (1 - q) *
            (δ * (1 - 2 * q - q ^ 2) * P - q ^ 3 * (1 + q) * R) *
              (q * h0) := by rw [← e0]
        _ = _ := by ring
    _ = q * (C * δ ^ 2 * P) := by rw [hBoundary]
    _ = C * ((1 - q) * (q * (1 - q) ^ 3 * P)) := by ring

end BoundaryAlgebra

private theorem actual_Z_eq_zeta : CatalyticH.Z = P13CatalanLagrangeBridge.zeta := by
  have hu : IsUnit ((1 + X : PowerSeries ℚ) ^ 2) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
  apply hu.mul_right_cancel
  rw [CatalyticH.Z_clear]
  change X = (X * P13CatalanLagrangeBridge.sourceUnitSqInv) *
    P13CatalanLagrangeBridge.sourceUnitSq
  rw [mul_assoc, P13CatalanLagrangeBridge.sourceUnitSq_inv_left, mul_one]

private theorem actual_A_eq_subst :
    CatalyticH.A = actualSeries.subst P13CatalanLagrangeBridge.zeta := by
  unfold CatalyticH.A
  rw [PowerSeries.coe_eval₂Hom, actual_Z_eq_zeta]
  unfold PowerSeries.subst PowerSeries.eval₂
  rw [MvPowerSeries.subst_eq_eval₂]
  rfl

/-- The transformed series of the original matching carrier is the explicit scalar G.
Every boundary and bulk law is supplied by the actual catalytic H. -/
theorem actual_A_eq_G : CatalyticH.A = P13Scalar.G := by
  have eScalar : ((1 - X : PowerSeries ℚ) ^ 2) ^ 2 * P13Scalar.P =
      (1 - X) ^ 2 * ((1 - X) ^ 2 - 2 * X ^ 2) * P13Scalar.R -
        X ^ 5 * P13Scalar.Phi 3 := by
    simpa only [P13Scalar.delta, P13Scalar.P, P13Scalar.R,
      Nat.reduceAdd, Nat.reduceMul] using P13Scalar.Phi_difference 1
  have eTail : (1 - X : PowerSeries ℚ) ^ 2 * P13Scalar.R * CatalyticH.h 2 +
      X ^ 2 * P13Scalar.Phi 3 * CatalyticH.h 1 = 0 := by
    simpa only [P13Scalar.R, Nat.reduceAdd, Nat.reduceSub] using
      CatalyticH.h_minimal_solution 2 (by decide)
  have cleared : (CatalyticH.A - 1) * P13Scalar.D =
      X * (1 - X) ^ 3 * P13Scalar.P := by
    simpa only [P13Scalar.D, P13Scalar.delta] using
      boundary_algebra CatalyticH.A (CatalyticH.h 0) (CatalyticH.h 1) (CatalyticH.h 2)
        P13Scalar.P P13Scalar.R (P13Scalar.Phi 3)
        CatalyticH.h_boundary_zero CatalyticH.h_boundary_one CatalyticH.h_boundary_two
        eTail eScalar
  have hu : IsUnit P13Scalar.D :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
  have eqsub : CatalyticH.A - 1 = P13Scalar.G - 1 :=
    hu.mul_right_cancel (cleared.trans P13Scalar.G_cleared.symm)
  simpa only [sub_left_inj] using eqsub

/-- A legal zero-constant substitution identifies the actual counting series with G. -/
theorem actualSeries_subst_zeta_eq_G :
    actualSeries.subst P13CatalanLagrangeBridge.zeta = P13Scalar.G := by
  rw [← actual_A_eq_subst, actual_A_eq_G]

private theorem recover_series (f g : PowerSeries ℚ)
    (he : f.subst P13CatalanLagrangeBridge.zeta = g) :
    f = g.subst P13CatalanLagrangeBridge.q := by
  have hz : HasSubst P13CatalanLagrangeBridge.zeta :=
    HasSubst.of_constantCoeff_zero' P13CatalanLagrangeBridge.zeta_constantCoeff
  have hq : HasSubst P13CatalanLagrangeBridge.q :=
    HasSubst.of_constantCoeff_zero' P13CatalanLagrangeBridge.q_constantCoeff
  have ha : PowerSeries.subst P13CatalanLagrangeBridge.q
      (PowerSeries.subst P13CatalanLagrangeBridge.zeta f) =
      PowerSeries.subst (PowerSeries.subst P13CatalanLagrangeBridge.q
        P13CatalanLagrangeBridge.zeta) f :=
    PowerSeries.subst_comp_subst_apply (R := ℚ) (S := ℚ) (T := ℚ) (υ := Unit)
      (a := P13CatalanLagrangeBridge.zeta) (b := P13CatalanLagrangeBridge.q) hz hq f
  have hi : PowerSeries.subst (PowerSeries.subst P13CatalanLagrangeBridge.q
      P13CatalanLagrangeBridge.zeta) f =
      PowerSeries.subst (PowerSeries.X : PowerSeries ℚ) f :=
    congrArg (fun s : PowerSeries ℚ => PowerSeries.subst s f)
      P13CatalanLagrangeBridge.zeta_subst_q
  have hx : PowerSeries.subst (PowerSeries.X : PowerSeries ℚ) f = f :=
    PowerSeries.X_subst f
  have hg : PowerSeries.subst P13CatalanLagrangeBridge.q
      (PowerSeries.subst P13CatalanLagrangeBridge.zeta f) =
      PowerSeries.subst P13CatalanLagrangeBridge.q g :=
    congrArg (fun s : PowerSeries ℚ => PowerSeries.subst P13CatalanLagrangeBridge.q s) he
  exact hx.symm.trans (hi.symm.trans (ha.symm.trans hg))

/-- Substitution by the Catalan root recovers the original series at every degree. -/
theorem actualSeries_eq_G_subst_q :
    actualSeries = P13Scalar.G.subst P13CatalanLagrangeBridge.q :=
  recover_series actualSeries P13Scalar.G actualSeries_subst_zeta_eq_G

/-- All-size enumeration for P13 = {132, 213, 321}, in the original perfect-matching
carrier. The empty matching has count one; the formula holds for every n ≥ 1. -/
theorem result :
    actualCount 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
      (actualCount n : ℚ) =
        coeff n ((1 - X) * (1 + X) ^ (2 * n - 1) * P13Scalar.G) := by
  refine ⟨actualCount_continuation.1, ?_⟩
  intro n hn
  calc
    (actualCount n : ℚ) = coeff n actualSeries := by simp [actualSeries]
    _ = coeff n (P13Scalar.G.subst P13CatalanLagrangeBridge.q) :=
      congrArg (coeff n) actualSeries_eq_G_subst_q
    _ = _ := P13CatalanLagrangeBridge.q_subst_coefficient_transform P13Scalar.G n hn

end

end D5.S3.Combinatorics.PatternMatchings.P13
