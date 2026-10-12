/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2FullAgreement
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2FullAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIIPSLnF2ResidualInner
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.PSLnF2Residual
open Matrix NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)

/-- Intrinsic projective U agreement extends to every actual quotient target
after a genuine projective inner correction, with no lift premise. -/
theorem U_agreement_inner_full (hF : Fintype.card F=2) (hn : 4<n)
    (beta delta : MulAut Q) (hU : ∀ x ∈ Uplus n F, beta (π x)=delta (π x)) :
    ∃ c : Q, ∀ x : Q, (MulAut.conj c*beta) x=delta x := by
  let gamma := delta⁻¹*beta
  have hgammaU : ∀ x ∈ Uplus n F, gamma (π x)=π x := by
    intro x hx
    change delta.symm (beta (π x))=π x
    rw [hU x hx,delta.symm_apply_apply]
  obtain ⟨c,_,_,hfull⟩ := pointwise_U_inner_correction hF hn gamma hgammaU
  refine ⟨delta c,?_⟩
  intro x
  have he := congrArg delta (hfull x)
  change delta (c*delta.symm (beta x)*c⁻¹)=delta x at he
  change delta c*beta x*(delta c)⁻¹=delta x
  simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply] using he

end NikolovSegal.PSLnF2Residual
