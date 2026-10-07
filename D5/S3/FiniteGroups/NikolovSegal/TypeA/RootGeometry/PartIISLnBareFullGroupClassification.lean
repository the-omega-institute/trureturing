/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareFullGroupClassification
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareFullGroupClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnPointwiseURigidity
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnPointwiseURigidity
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnFullGroupGeneration
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnStandardTorusStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnFullGroup
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F

/-- The missing full-group rigidity: whole-U fixation and actual T preservation
force fixation of EVERY actual SLn target. Opposite-root action and generation
are proved, not supplied as hypotheses. -/
theorem pointwise_U_T_rigid (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F) (gamma : MulAut G)
    (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (hT : (T).map gamma.toMonoidHom=T) : ∀ x, gamma x=x := by
  apply hom_ext_positive_negative_simple (by omega) gamma.toMonoidHom (MonoidHom.id G)
  · intro r t; exact hU _ (root_mem_Uplus r t)
  · intro r hr t; exact fixes_negative_simple p hn hF gamma hU hT r hr t

/-- Genuine U agreement between actual automorphisms extends to the whole
SLn group when both preserve the actual diagonal torus. -/
theorem U_T_agreement_full (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F) (beta delta : MulAut G)
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

/-- Bare actual SLn automorphism classification on the WHOLE group in the
proved branch n>=3/cardF>4. ONE determinant-one inner correction and ONE
DFG tuple are chosen BEFORE ALL full-group targets. -/
theorem sl_bare_full_group_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F) (alpha : MulAut G) :
    ∃ c : G, ∃ a : Fin n → Fˣ, ∃ phi : RingAut F, ∃ eps : Bool,
      ∀ x : G, (MulAut.conj c*alpha) x=diagonalFieldGraph a phi eps x := by
  obtain ⟨c,a,phi,eps,_,hT,hU⟩ := sl_bare_full_U_diagonal_field_graph p hn hF alpha
  exact ⟨c,a,phi,eps,U_T_agreement_full p hn hF _ _ hT
    (diagonalFieldGraph_map_torus a phi eps) hU⟩
end NikolovSegal.SLnFullGroup

