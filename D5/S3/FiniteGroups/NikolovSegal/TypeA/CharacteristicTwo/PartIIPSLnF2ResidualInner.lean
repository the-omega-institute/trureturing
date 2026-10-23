/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2ResidualInner
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2ResidualInner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2ResidualInner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.PSLnF2Residual
open Matrix NikolovSegal.SLnNormalizer NikolovSegal.PSLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)

/-- Genuine centre-trivial quotient bijectivity over a two-element field. -/
theorem quotient_bijective (hF : Fintype.card F=2) (hn : 0<n) : Function.Bijective π := by
  refine ⟨?_,QuotientGroup.mk'_surjective (Subgroup.center G)⟩
  intro x y hxy
  have hc : x/y ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp hxy
  have he := NikolovSegal.SLnF2Residual.center_eq_one hF hn (x/y) hc
  exact div_eq_one.mp he

/-- The actual quotient map is an isomorphism here, proved from matrix centre
triviality. No lift of the prescribed projective automorphism is assumed. -/
noncomputable def quotientEquiv (hF : Fintype.card F=2) (hn : 0<n) : G ≃* Q :=
  MulEquiv.ofBijective π (quotient_bijective hF hn)

variable [CharP F 2]

/-- The intrinsic projective F2 residual is removed by ONE actual projective
central-U inner correction before every full quotient target. -/
theorem pointwise_U_inner_correction (hF : Fintype.card F=2) (hn : 4<n)
    (gamma : MulAut Q) (hU : ∀ x ∈ Uplus n F, gamma (π x)=π x) :
    ∃ c ∈ projectiveUplus n F, (∀ x ∈ projectiveUplus n F, c*x=x*c) ∧
      ∀ x : Q, (MulAut.conj c*gamma) x=x := by
  let e := quotientEquiv (F := F) hF (by omega : 0<n)
  let gammaSL : MulAut G := e.trans (gamma.trans e.symm)
  have he : ∀ x : G, e x=π x := fun _ => rfl
  have hgamma : ∀ x : G, π (gammaSL x)=gamma (π x) := by
    intro x
    change e (e.symm (gamma (e x)))=gamma (π x)
    rw [e.apply_symm_apply,he]
  have hSLU : ∀ x ∈ Uplus n F, gammaSL x=x := by
    intro x hx
    apply e.injective
    change π (gammaSL x)=π x
    rw [hgamma,hU x hx]
  obtain ⟨c,hc,hcomm,hfull⟩ := NikolovSegal.SLnF2Residual.pointwise_U_inner_correction hF hn gammaSL hSLU
  refine ⟨π c,Subgroup.mem_map_of_mem π hc,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    simpa only [map_mul] using congrArg π (hcomm x hx)
  · intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    have heq := congrArg π (hfull x)
    change π (c*gammaSL x*c⁻¹)=π x at heq
    change π c*gamma (π x)*(π c)⁻¹=π x
    simpa only [map_mul,map_inv,hgamma] using heq

end NikolovSegal.PSLnF2Residual
