/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2BareFullGroup
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2BareFullGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2BareFullGroup
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace NikolovSegal.PSLnF2Bare
open Matrix NikolovSegal.SLnF2Bare
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)

/-- Intrinsic bare PSLn over EVERY two-element field, EVERY n>=5. The actual
quotient isomorphism is PROVED in the frozen F2 residual input, not assumed
as an automorphism-lift premise. One actual projective inner correction and
graph choice precede EVERY SL representative. -/
theorem psl_bare_full_group_inner_graph (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut Q) :
    ∃ c : Q, ∃ eps : Bool, ∀ x : G,
      (MulAut.conj c*alpha) (π x)=
        π (diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps x) := by
  let e := NikolovSegal.PSLnF2Residual.quotientEquiv (F := F) hF (by omega : 0<n)
  have heq : ∀ x : G, e x=π x := fun _ => rfl
  let alphaSL : MulAut G := e.trans (alpha.trans e.symm)
  obtain ⟨c,eps,hfull⟩ := sl_bare_full_group_inner_graph hF hn alphaSL
  refine ⟨π c,eps,?_⟩
  intro x
  have he := congrArg e (hfull x)
  change e (c*e.symm (alpha (e x))*c⁻¹)=
    e (diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps x) at he
  change π c*alpha (π x)*(π c)⁻¹=
    π (diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps x)
  simp only [map_mul,map_inv] at he
  rw [e.apply_symm_apply] at he
  simpa only [heq] using he

/-- Literal equality on ALL quotient targets with the native induced central
quotient action, without an alpha-lift assumption. -/
theorem psl_bare_full_group_inner_graph_aut (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut Q) :
    ∃ c : Q, ∃ eps : Bool,
      MulAut.conj c*alpha=QuotientGroup.congr _ _
        (diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps)
        (Subgroup.characteristic_iff_map_eq.mp inferInstance _) := by
  obtain ⟨c,eps,hfull⟩ := psl_bare_full_group_inner_graph hF hn alpha
  refine ⟨c,eps,?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
  exact hfull x

end NikolovSegal.PSLnF2Bare
