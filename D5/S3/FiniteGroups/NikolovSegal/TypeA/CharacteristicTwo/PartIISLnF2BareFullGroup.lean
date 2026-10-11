/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2BareFullGroup
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2BareFullGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2WholeU
import Mathlib.Algebra.CharP.CharAndCard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.InnerUNormalization
open NikolovSegal.PartIIUnitriangularActions NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- Bind the graph choice to the exact accepted DFG convention. -/
theorem trivial_diagonal_field_graph (eps : Bool) :
    diagonalFieldGraph (fun _ : Fin n => (1:Fˣ)) (RingEquiv.refl F) eps=
      (if eps then positiveGraph else 1 : MulAut G) := by
  have hd : (unitOdd% diagonalAut) (fun _ : Fin n => (1:Fˣ))=(1 : MulAut G) := by
    apply MulEquiv.ext
    intro x
    apply SpecialLinearGroup.ext
    intro i j
    rw [(unitOdd% diagonal_entry)]
    simp
  have hf : fieldAut (RingEquiv.refl F)=(1 : MulAut G) := by
    apply MulEquiv.ext
    intro x
    apply SpecialLinearGroup.ext
    intro i j
    rfl
  simp only [diagonalFieldGraph,fieldGraphAut,hd,hf,one_mul]

/-- F2 whole-U bare normalization with one genuine inner correction BEFORE
all U targets. The characteristic is derived from the actual cardinality. -/
theorem sl_bare_whole_U_inner_graph (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) :
    ∃ c : G, ∃ eps : Bool, ∀ x ∈ Uplus n F,
      (MulAut.conj c*alpha) x=diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps x := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : CharP F 2 := charP_of_card_eq_prime hF
  obtain ⟨c0,hU,_,_,_⟩ := sl_inner_U_Borel_correction (F := F) 2 n alpha
  let beta : MulAut G := MulAut.conj c0*alpha
  obtain ⟨c1,_,eps,hagree⟩ := normalized_whole_U_inner_graph hF hn beta hU
  refine ⟨c1*c0,eps,?_⟩
  intro x hx
  rw [trivial_diagonal_field_graph]
  have he := hagree x hx
  change c1*(c0*alpha x*c0⁻¹)*c1⁻¹=_ at he
  change (c1*c0)*alpha x*(c1*c0)⁻¹=_
  simpa only [_root_.mul_inv_rev,mul_assoc] using he

/-- Bare actual SLn over EVERY two-element field, EVERY n>=5. ONE actual
inner correction and graph choice precede EVERY full-group target. The
whole-U proof and the necessary central-U residual are both consumed. -/
theorem sl_bare_full_group_inner_graph (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) :
    ∃ c : G, ∃ eps : Bool, ∀ x : G,
      (MulAut.conj c*alpha) x=diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps x := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : CharP F 2 := charP_of_card_eq_prime hF
  obtain ⟨c0,eps,hU⟩ := sl_bare_whole_U_inner_graph hF hn alpha
  obtain ⟨c1,hfull⟩ := NikolovSegal.SLnF2Residual.U_agreement_inner_full hF hn
    (MulAut.conj c0*alpha) (diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps) hU
  refine ⟨c1*c0,eps,?_⟩
  intro x
  have he := hfull x
  change c1*(c0*alpha x*c0⁻¹)*c1⁻¹=_ at he
  change (c1*c0)*alpha x*(c1*c0)⁻¹=_
  simpa only [_root_.mul_inv_rev,mul_assoc] using he

/-- Actual MulAut equality, rather than just restriction to U. -/
theorem sl_bare_full_group_inner_graph_aut (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) :
    ∃ c : G, ∃ eps : Bool,
      MulAut.conj c*alpha=diagonalFieldGraph (fun _ => (1:Fˣ)) (RingEquiv.refl F) eps := by
  obtain ⟨c,eps,h⟩ := sl_bare_full_group_inner_graph hF hn alpha
  exact ⟨c,eps,MulEquiv.ext h⟩

end NikolovSegal.SLnF2Bare
