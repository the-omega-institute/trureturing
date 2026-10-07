/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FullAgreement
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2FullAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIIPSLnF2ResidualInner
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Residual
open Matrix NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- Actual U agreement over F2 extends to the whole SL group AFTER a further
genuine inner correction. This retains the necessary residual freedom. -/
theorem U_agreement_inner_full (hF : Fintype.card F=2) (hn : 4<n)
    (beta delta : MulAut G) (hU : ∀ x ∈ Uplus n F, beta x=delta x) :
    ∃ c : G, ∀ x : G, (MulAut.conj c*beta) x=delta x := by
  let gamma := delta⁻¹*beta
  have hgammaU : ∀ x ∈ Uplus n F, gamma x=x := by
    intro x hx
    change delta.symm (beta x)=x
    rw [hU x hx,delta.symm_apply_apply]
  obtain ⟨c,_,_,hfull⟩ := pointwise_U_inner_correction hF hn gamma hgammaU
  refine ⟨delta c,?_⟩
  intro x
  have he := congrArg delta (hfull x)
  change delta (c*delta.symm (beta x)*c⁻¹)=delta x at he
  change delta c*beta x*(delta c)⁻¹=delta x
  simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply] using he

end NikolovSegal.SLnF2Residual

