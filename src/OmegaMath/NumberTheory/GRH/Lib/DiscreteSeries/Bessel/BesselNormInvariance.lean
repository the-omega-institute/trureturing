import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.CuspKernel.BesselSchurBound
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bessel subgroup of a real unitary group: coordinates, Haar measure, Bessel functions
(known result; see Lib.DiscreteSeries.Bessel.RealMeasures).

This file: Norms of a Bessel function and of its means are invariant under Bessel subgroup. -/

namespace IsBesselFunction

open MeasureTheory
variable {𝔰 I} [Fintype I] {rep W} (hW : @IsBesselFunction 𝔰 I _ rep W) {s : 𝔰.G₁} (hs :
  s ∈ besselS)
include hW hs

lemma enorm_integral_besselS_mul (β : _ → ℂ) g {μ : Measure _} :
    ‖∫ y, β y • W (s * g * y) ∂μ‖ₑ = ‖∫ y, β y • W (g * y) ∂μ‖ₑ := by
  obtain ⟨u, a, h, rfl⟩ := exists_besselU_mul_toBesselH hs
  rw [eq_comm, ← (Unitary.linearIsometryEquiv (besselValueRep rep h)).toLinearIsometry.enorm_map,
    ← LinearIsometry.integral_comp_comm]
  simp [mul_assoc, hW.2, hW.3, smul_comm (β _), integral_smul, ← ofReal_norm, norm_smul, a]; rfl

lemma enorm_besselS_mul y : ‖W (s * y)‖ₑ = ‖W
  y‖ₑ := by simpa using hW.enorm_integral_besselS_mul hs 1 y (μ := .dirac 1)
