/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3TorusAlignment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3TorusAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3RootGeometry
import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3UnipotentNormalizer
import D5.S3.FiniteGroups.NikolovSegal.PartIIA2TorusAlignment
import Mathlib.GroupTheory.Index

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Lean Elab Term in
elab "sl3Torus%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIA2TorusAlignment"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ owner
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual torus theorem {id} not found"
namespace NikolovSegal.PartIIPSL3TorusAlignment
open PartIIPSL3Unipotent PartIIPSL3UnipotentNormalizer PartIIPSL3RootGeometry
open PartIIA2Orbital PartIIA2TorusAlignment Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev pi : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (Subgroup.center _)

def projectiveDiagonalTorus : Subgroup PSL(3,F) := (diagonalTorus (F := F)).map pi

private theorem center_le_torus : (pi (F := F)).ker ≤ diagonalTorus := by
  intro g hg
  have hc : g ∈ Subgroup.center SL(3,F) := (QuotientGroup.eq_one_iff g).mp hg
  apply (sl3Torus% mem_torus_of_diagonal) g (fun _ => g 0 0)
  exact (scalar_eq_self_of_mem_center hc 0).symm

private theorem card_torus_image_preimage [Fintype F] [DecidableEq F]
    (beta : MulAut PSL(3,F)) :
    Nat.card ((projectiveDiagonalTorus (F := F)).map beta.toMonoidHom |>.comap pi)=
      (Fintype.card F-1)^2 := by
  let W := ((projectiveDiagonalTorus (F := F)).map beta.toMonoidHom).comap pi
  have hi : W.index=(diagonalTorus (F := F)).index := by
    dsimp only [W]
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hb : ((projectiveDiagonalTorus (F := F)).map beta.toMonoidHom).index=
        (projectiveDiagonalTorus (F := F)).index := Subgroup.index_map_equiv _ beta
    rw [hb]
    exact Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) center_le_torus
  have hc : Nat.card W=Nat.card (diagonalTorus (F := F)) := by
    apply (mul_left_inj' (diagonalTorus (F := F)).index_ne_zero_of_finite).mp
    calc
      Nat.card W*(diagonalTorus (F := F)).index=Nat.card W*W.index := by rw [hi]
      _ = Nat.card SL(3,F) := W.card_mul_index
      _ = Nat.card (diagonalTorus (F := F))*(diagonalTorus (F := F)).index :=
        (diagonalTorus (F := F)).card_mul_index.symm
  exact hc.trans (sl3Torus% card_diagonalTorus)

private theorem projective_torus_le_normalizer : projectiveDiagonalTorus (F := F) ≤
    Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F)) := by
  rintro g ⟨t,⟨x,rfl⟩,rfl⟩
  apply (quotient_mem_normalizer_iff _).mpr
  apply (PartIISL3UnipotentNormalizer.mem_normalizer_iff_upper _).mpr
  intro i j hij
  change Matrix.diagonal _ i j=0
  simp [Matrix.diagonal_apply,ne_of_gt hij]

/-- The actual projective torus image is aligned by averaging its WHOLE
SL3 preimage. Native index arithmetic proves the preimage has exactly the
original torus order, including nontrivial scalar centres. There is no
projective-auto lift, torus-image, coprimality or coverage premise. -/
theorem actual_projective_U_torus_alignment [Fintype F] [DecidableEq F]
    (beta : MulAut PSL(3,F))
    (hU : (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom=projectiveUpperUnipotent) :
    ∃ u : SL(3,F), u ∈ upperUnipotent ∧
      (projectiveUpperUnipotent (F := F)).map (MulAut.conj (pi u)⁻¹*beta).toMonoidHom=
        projectiveUpperUnipotent ∧
      (projectiveDiagonalTorus (F := F)).map (MulAut.conj (pi u)⁻¹*beta).toMonoidHom=
        projectiveDiagonalTorus := by
  classical
  let W := ((projectiveDiagonalTorus (F := F)).map beta.toMonoidHom).comap pi
  letI : Fintype W := Fintype.ofFinite _
  have htri : ∀ w : W, ∀ i j : Fin 3, j < i → (w:SL(3,F)) i j=0 := by
    intro w
    have hm : pi w.val ∈ (Subgroup.normalizer
        (projectiveUpperUnipotent (F := F) : Set PSL(3,F))).map beta.toMonoidHom :=
      (Subgroup.map_mono projective_torus_le_normalizer) w.prop
    rw [automorphism_projective_normalizer_map beta hU] at hm
    exact (PartIISL3UnipotentNormalizer.mem_normalizer_iff_upper w.val).mp
      ((quotient_mem_normalizer_iff w.val).mp hm)
  have hc : Fintype.card W=(Fintype.card F-1)^2 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_torus_image_preimage beta
  have hfc : ((Fintype.card F-1:ℕ):F)= -1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))),
      FiniteField.cast_card_eq_zero,Nat.cast_one,zero_sub]
  have hcast : (Fintype.card W:F) ≠ 0 := by
    rw [hc,Nat.cast_pow,hfc]
    exact pow_ne_zero 2 (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨u,hu,hdiag⟩ := upper_finite_subgroup_diagonal_alignment W htri hcast
  let delta := MulAut.conj (pi u)⁻¹*beta
  have hV : (projectiveUpperUnipotent (F := F)).map delta.toMonoidHom=projectiveUpperUnipotent := by
    change (projectiveUpperUnipotent (F := F)).map
      ((MulAut.conj (pi u)⁻¹).toMonoidHom.comp beta.toMonoidHom)=_
    rw [← Subgroup.map_map,hU]
    have hum : pi u ∈ projectiveUpperUnipotent := Subgroup.mem_map_of_mem pi hu
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (projectiveUpperUnipotent.inv_mem hum))
  have hle : (projectiveDiagonalTorus (F := F)).map delta.toMonoidHom ≤ projectiveDiagonalTorus := by
    rintro g ⟨z,⟨t,ht,rfl⟩,rfl⟩
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) (beta (pi t))
    have hwW : w ∈ W := by
      change pi w ∈ (projectiveDiagonalTorus (F := F)).map beta.toMonoidHom
      rw [hw]
      exact Subgroup.mem_map_of_mem beta.toMonoidHom (Subgroup.mem_map_of_mem pi ht)
    have hd : u⁻¹*w*u ∈ diagonalTorus := (sl3Torus% mem_torus_of_diagonal) _ _ (hdiag ⟨w,hwW⟩)
    refine ⟨u⁻¹*w*u,hd,?_⟩
    change pi (u⁻¹*w*u)=(MulAut.conj (pi u)⁻¹*beta) (pi t)
    simp only [map_mul,map_inv,hw,MulAut.mul_apply,MulAut.conj_apply,MulAut.conj_inv_apply,inv_inv]
  have hT : (projectiveDiagonalTorus (F := F)).map delta.toMonoidHom=projectiveDiagonalTorus := by
    apply Subgroup.eq_of_le_of_card_ge hle
    exact (Nat.card_congr ((projectiveDiagonalTorus (F := F)).equivMapOfInjective
      delta.toMonoidHom delta.injective).toEquiv).le
  exact ⟨u,hu,hV,hT⟩

/-- Every bare PSL3 automorphism over every finite field has ONE projective
inner normalization preserving U,T and the computed central root. The
scalar centre is retained in the averaging preimage; no SL3 lift is used. -/
theorem actual_bare_PSL3_U_T_central_root_normalization [Fintype F] [DecidableEq F]
    (beta : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F),
      (projectiveUpperUnipotent (F := F)).map (MulAut.conj g⁻¹*beta).toMonoidHom=
        projectiveUpperUnipotent ∧
      (projectiveDiagonalTorus (F := F)).map (MulAut.conj g⁻¹*beta).toMonoidHom=
        projectiveDiagonalTorus ∧
      (projectivePositiveRoot (F := F) 2).map (MulAut.conj g⁻¹*beta).toMonoidHom=
        projectivePositiveRoot 2 := by
  obtain ⟨g,hU,_⟩ := actual_bare_PSL3_U_central_root_normalization beta
  obtain ⟨u,_,hV,hT⟩ := actual_projective_U_torus_alignment (MulAut.conj g⁻¹*beta) hU
  have he : MulAut.conj (g*pi u)⁻¹*beta=MulAut.conj (pi u)⁻¹*(MulAut.conj g⁻¹*beta) := by
    rw [mul_inv_rev,map_mul,mul_assoc]
  refine ⟨g*pi u,?_,?_,?_⟩
  · rw [he]; exact hV
  · rw [he]; exact hT
  · rw [he]; exact actual_projective_U_preserving_central_root_map _ hV
end NikolovSegal.PartIIPSL3TorusAlignment
