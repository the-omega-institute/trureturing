/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallFullGroup
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallFullGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallUClassification
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallOppositeRigidity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnSmallField
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F
open NikolovSegal.SLnFullGroup
variable [Fintype F]

theorem pointwise_U_T_rigid (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (gamma : MulAut G)
    (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (hT : (T).map gamma.toMonoidHom=T) : ∀ x, gamma x=x := by
  apply hom_ext_positive_negative_simple (by omega) gamma.toMonoidHom (MonoidHom.id G)
  · intro r t; exact hU _ (root_mem_Uplus r t)
  · intro r hr t; exact fixes_negative_simple p hn hF gamma hU hT r hr t

theorem U_T_agreement_full (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (beta delta : MulAut G)
    (hb : (T).map beta.toMonoidHom=T) (hd : (T).map delta.toMonoidHom=T)
    (hU : ∀ x ∈ Uplus n F, beta x=delta x) : ∀ x, beta x=delta x := by
  let gamma := delta⁻¹*beta
  have hgammaU : ∀ x ∈ Uplus n F, gamma x=x := by
    intro x hx
    change delta.symm (beta x)=x
    rw [hU x hx]
    exact delta.symm_apply_apply x
  have hgammaT := relative_map_subgroup (T) beta delta hb hd
  intro x
  have he := pointwise_U_T_rigid p hn hF gamma hgammaU hgammaT x
  change delta.symm (beta x)=x at he
  apply delta.symm.injective
  simpa only [MulEquiv.symm_apply_apply] using he

theorem sl_bare_full_group_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (alpha : MulAut G) :
    ∃ c : G, ∃ a : Fin n → Fˣ, ∃ phi : RingAut F, ∃ eps : Bool,
      ∀ x : G, (MulAut.conj c*alpha) x=diagonalFieldGraph a phi eps x := by
  obtain ⟨c,a,phi,eps,_,hT,hU⟩ := sl_bare_full_U_diagonal_field_graph p hn hF alpha
  exact ⟨c,a,phi,eps,U_T_agreement_full p hn hF _ _ hT
    (diagonalFieldGraph_map_torus a phi eps) hU⟩

end NikolovSegal.SLnSmallField

namespace NikolovSegal.PSLnSmallField
open Matrix NikolovSegal.SLnRootAction NikolovSegal.PSLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
open NikolovSegal.SLnSmallField NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)
local notation "T" => diagonalTorus n F
open NikolovSegal.SLnFullGroup
variable [Fintype F]

theorem pointwise_U_T_rigid (hn : 4 < n) (hF : 2 < Fintype.card F) (gamma : MulAut Q)
    (hU : ∀ x ∈ Uplus n F, gamma (π x)=π x)
    (hT : (projectiveDiagonalTorus n F).map gamma.toMonoidHom=projectiveDiagonalTorus n F) :
    ∀ x : G, gamma (π x)=π x := by
  apply hom_ext_positive_negative_simple (by omega) (gamma.toMonoidHom.comp π) π
  · intro r t; exact hU _ (root_mem_Uplus r t)
  · intro r hr t; exact fixes_negative_simple hn hF gamma hU hT r hr t

theorem U_T_agreement_full (hn : 4 < n) (hF : 2 < Fintype.card F)
    (beta : MulAut Q) (delta : MulAut G)
    (hb : (projectiveDiagonalTorus n F).map beta.toMonoidHom=projectiveDiagonalTorus n F)
    (hd : (diagonalTorus n F).map delta.toMonoidHom=diagonalTorus n F)
    (hU : ∀ x ∈ Uplus n F, beta (π x)=π (delta x)) :
    ∀ x : G, beta (π x)=π (delta x) := by
  let dq : MulAut Q := QuotientGroup.congr _ _ delta
    (Subgroup.characteristic_iff_map_eq.mp inferInstance delta)
  have hdq : (projectiveDiagonalTorus n F).map dq.toMonoidHom=projectiveDiagonalTorus n F := by
    change ((diagonalTorus n F).map π).map dq.toMonoidHom=(diagonalTorus n F).map π
    rw [Subgroup.map_map]
    have he : dq.toMonoidHom.comp π=(π).comp delta.toMonoidHom := by ext x; rfl
    rw [he,← Subgroup.map_map,hd]
  let gamma := dq⁻¹*beta
  have hgammaU : ∀ x ∈ Uplus n F, gamma (π x)=π x := by
    intro x hx
    change dq.symm (beta (π x))=π x
    rw [hU x hx]
    change dq.symm (dq (π x))=π x
    exact dq.symm_apply_apply (π x)
  have hgammaT := relative_map_subgroup (projectiveDiagonalTorus n F) beta dq hb hdq
  intro x
  have he := pointwise_U_T_rigid hn hF gamma hgammaU hgammaT x
  change dq.symm (beta (π x))=π x at he
  apply dq.symm.injective
  change dq.symm (beta (π x))=dq.symm (dq (π x))
  simpa only [MulEquiv.symm_apply_apply] using he

theorem psl_bare_full_group_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (alpha : MulAut Q) :
    ∃ c : Q, ∃ a : Fin n → Fˣ, ∃ phi : RingAut F, ∃ eps : Bool,
      ∀ x : G, (MulAut.conj c*alpha) (π x)=π (diagonalFieldGraph a phi eps x) := by
  obtain ⟨c,a,phi,eps,_,hT,hU⟩ := psl_bare_full_U_diagonal_field_graph p hn hF alpha
  exact ⟨c,a,phi,eps,U_T_agreement_full hn hF _ _ hT
    (diagonalFieldGraph_map_torus a phi eps) hU⟩

end NikolovSegal.PSLnSmallField
