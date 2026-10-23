/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2WholeU
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2WholeU
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2FrameAlignment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.SLnF2Residual
open NikolovSegal.PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- A normalized bare automorphism with identity simple pivots agrees with
ONE actual U-inner automorphism on the WHOLE U. -/
theorem identity_pivots_inner_on_U (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F)
    (hp : ∀ i, simpleEntry (alpha (root (simpleRoot i) 1)) i=1) :
    ∃ C : G, C ∈ Uplus n F ∧ ∀ x ∈ Uplus n F, alpha x=(MulAut.conj C) x := by
  let X : Fin (n-1) → G := fun i => alpha (root (simpleRoot i) 1)
  have hu : ∀ i, X i ∈ Uplus n F := by
    intro i; rw [← hU]; exact Subgroup.mem_map_of_mem _ (root_mem_Uplus _ _)
  have hm : ∀ i a b d e, deviation (X i) a b*deviation (X i) d e=deviation (X i) a e*deviation (X i) d b := by
    intro i; exact normalized_transvection_image_minors hF hn alpha hU _ _ _
  have hpair : ∀ i j, framePairing X i j=if j.val=i.val+1 then 1 else 0 := by
    intro i j
    by_cases hij : j.val=i.val+1
    · rw [if_pos hij]
      exact normalized_frame_pairing_adjacent hF hn alpha hU hp i j hij
    · rw [if_neg hij]
      by_cases hle : j.val ≤ i.val
      · exact frame_pairing_zero_le X hu i j hle
      · exact normalized_frame_pairing_far hF hn alpha hU hp i j (by omega)
  let C := frameSL X hn hu hp
  refine ⟨C,frameSL_mem_Uplus X hn hu hp,?_⟩
  apply hom_ext_on_simple_roots alpha.toMonoidHom (MulAut.conj C).toMonoidHom
  intro i t
  rcases eq_zero_or_one hF t with ht|ht
  · subst t; simp [root]
  · subst t
    exact (frameSL_conjugates X hn hu hp hm hpair i).symm

theorem reflect_simpleRoot (i : Fin (n-1)) : reflectRoot (simpleRoot i)=simpleRoot i.rev := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    simp only [reflectRoot,simpleRoot,Fin.val_rev]
    have hi:=i.isLt
    omega

/-- The accepted actual graph convention is involutive on U by its genuine
simple-root law and the accepted generation proof. -/
theorem positiveGraph_twice_U : ∀ x ∈ Uplus n F, positiveGraph (positiveGraph x)=x := by
  apply hom_ext_on_simple_roots
    (positiveGraph.toMonoidHom.comp (positiveGraph (F := F) (n := n)).toMonoidHom) (MonoidHom.id G)
  intro i t
  change positiveGraph (positiveGraph (root (simpleRoot i) t))=root (simpleRoot i) t
  rw [positiveGraph_simple_root,reflect_simpleRoot,positiveGraph_simple_root,
    reflect_simpleRoot,Fin.rev_rev]

/-- Actual graph U stability, proved using literal simple roots. -/
theorem positiveGraph_map_Uplus : (Uplus n F).map (positiveGraph (F := F) (n := n)).toMonoidHom=Uplus n F := by
  have hinto : ∀ x ∈ Uplus n F, positiveGraph x ∈ Uplus n F := by
    have hle := Uplus_le_of_simple_roots
      ((Uplus n F).comap (positiveGraph (F := F) (n := n)).toMonoidHom) (by
      intro i t
      change positiveGraph (root (simpleRoot i) t) ∈ Uplus n F
      rw [positiveGraph_simple_root]
      exact root_mem_Uplus _ _)
    exact hle
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact hinto y hy
  · intro x hx
    exact ⟨positiveGraph x,hinto x hx,positiveGraph_twice_U x hx⟩

/-- The genuinely missing F2 whole-U agreement: a bare U-normalized
full-group automorphism has only inner and positive-graph action on U.
The pivot permutation and simultaneous conjugator are DERIVED. -/
theorem normalized_whole_U_inner_graph (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F) :
    ∃ c : G, c ∈ Uplus n F ∧ ∃ eps : Bool,
      ∀ x ∈ Uplus n F, (MulAut.conj c*alpha) x=(if eps then positiveGraph else 1 : MulAut G) x := by
  obtain ⟨sigma,hcase,hp⟩ := normalized_pivots_identity_or_reflection hF hn alpha hU
  rcases hcase with hid|hrev
  · have hp' : ∀ i, simpleEntry (alpha (root (simpleRoot i) 1)) i=1 := by
      intro i; simpa only [hid] using (hp i).1
    obtain ⟨C,hC,hagree⟩ := identity_pivots_inner_on_U hF hn alpha hU hp'
    refine ⟨C⁻¹,(Uplus n F).inv_mem hC,false,?_⟩
    intro x hx
    change C⁻¹*alpha x*(C⁻¹)⁻¹=x
    rw [hagree x hx]
    change C⁻¹*(C*x*C⁻¹)*(C⁻¹)⁻¹=x
    group
  · let gamma : MulAut G := alpha*positiveGraph
    have hgammaU : (Uplus n F).map gamma.toMonoidHom=Uplus n F := by
      change (Uplus n F).map (alpha.toMonoidHom.comp positiveGraph.toMonoidHom)=Uplus n F
      rw [← Subgroup.map_map,positiveGraph_map_Uplus,hU]
    have hp' : ∀ i, simpleEntry (gamma (root (simpleRoot i) 1)) i=1 := by
      intro i
      change simpleEntry (alpha (positiveGraph (root (simpleRoot i) 1))) i=1
      rw [positiveGraph_simple_root,reflect_simpleRoot]
      have he := (hp i.rev).1
      simpa only [hrev,Fin.rev_rev] using he
    obtain ⟨C,hC,hagree⟩ := identity_pivots_inner_on_U hF hn gamma hgammaU hp'
    refine ⟨C⁻¹,(Uplus n F).inv_mem hC,true,?_⟩
    intro x hx
    have hxg : positiveGraph x ∈ Uplus n F := by
      rw [← positiveGraph_map_Uplus]
      exact Subgroup.mem_map_of_mem _ hx
    have he := hagree (positiveGraph x) hxg
    change alpha (positiveGraph (positiveGraph x))=C*positiveGraph x*C⁻¹ at he
    rw [positiveGraph_twice_U x hx] at he
    change C⁻¹*alpha x*(C⁻¹)⁻¹=positiveGraph x
    rw [he]
    group

end NikolovSegal.SLnF2Bare
