/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentDecomposition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIICentralLeviProduct
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIPropositionSixSeven
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
/-! Part II p255: the actual matrix equality U = U1 V. -/
open Lean Elab Term in
elab "centralKernel%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIICentralLevi"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIICentralLevi"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual central Levi kernel {id} not found"
namespace NikolovSegal.PartIIAmbientUnipotentDecomposition
open Matrix PartIIUnitriangularLayers PartIICentralLevi PartIIRadicalCoordinates
universe u
variable {F : Type u} [Field F] {n : ℕ}
private theorem middle_inj : Function.Injective (middle : Fin n → Fin (n+2)) := by
  intro i j h; apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [middle,Fin.val_succ,Fin.val_castSucc] at hh
  omega
private theorem central_det (b : SpecialLinearGroup (Fin (n+2)) F)
    (hb : LayerDepth 1 (b.val-1)) : det (b.val.submatrix middle middle)=1 := by
  classical
  have ht : IsUpperTriangular (b.val.submatrix middle middle) := by
    intro i j hij
    have hne : middle i≠middle j := fun h => (ne_of_gt hij) (middle_inj h)
    have he := hb (middle i) (middle j) (by change j.val+1 < i.val+1+1; change j.val < i.val at hij; omega)
    simpa only [Matrix.sub_apply,Matrix.one_apply,if_neg hne,sub_zero,Matrix.submatrix_apply] using he
  rw [det_of_isUpperTriangular ht]
  apply Finset.prod_eq_one
  intro i hi
  have he := hb (middle i) (middle i) (by omega)
  simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true,sub_eq_zero,Matrix.submatrix_apply] using he
/-- Actual central principal SL block of an arbitrary ambient U target. -/
def centralPart (b : SpecialLinearGroup (Fin (n+2)) F)
    (hb : LayerDepth 1 (b.val-1)) : SpecialLinearGroup (Fin n) F :=
  ⟨b.val.submatrix middle middle,central_det b hb⟩
theorem actual_central_part_unitriangular (b : SpecialLinearGroup (Fin (n+2)) F)
    (hb : LayerDepth 1 (b.val-1)) : LayerDepth 1 ((centralPart b hb).val-1) := by
  intro i j hij
  have he := hb (middle i) (middle j) (by change j.val+1 < i.val+1+1; change j.val < i.val+1 at hij; omega)
  simpa only [centralPart,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.one_apply,
    middle_inj.eq_iff] using he
private theorem index_first_any (i : Fin 1) :
    (centralKernel% indexEquiv) (Sum.inl i)=(0:Fin (n+2)) := by
  have hi : i=0 := Subsingleton.elim _ _
  rw [hi]; exact centralKernel% index_first
private theorem index_last_any (i : Fin 1) :
    (centralKernel% indexEquiv) (Sum.inr (Sum.inr i))=Fin.last (n+1) := by
  have hi : i=0 := Subsingleton.elim _ _
  rw [hi]; exact centralKernel% index_last
/-- The genuine Levi embedding preserves upper unitriangularity. -/
theorem actual_central_embed_unitriangular (g : SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1)) : LayerDepth 1 ((embed g).val-1) := by
  intro i j hij
  obtain ⟨i,rfl⟩ := (centralKernel% indexEquiv).surjective i
  obtain ⟨j,rfl⟩ := (centralKernel% indexEquiv).surjective j
  simp only [Matrix.sub_apply,centralKernel% entry,Matrix.one_apply]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp only [index_first_any,index_last_any,centralKernel% index_middle,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.one_apply,Matrix.zero_apply] at *
  · have he : i=j := Subsingleton.elim _ _; simp [he]
  · simp [middle,Fin.ext_iff]
  · simp [Fin.ext_iff]
  · simp [middle,Fin.ext_iff]
  · have he := hg i j (by change j.val < i.val+1; simp only [middle,Fin.val_succ,Fin.val_castSucc] at hij; omega)
    simpa only [Matrix.sub_apply,Matrix.one_apply,middle_inj.eq_iff] using he
  · have hne : middle i≠Fin.last (n+1) := by
      intro h; have hh := congrArg Fin.val h
      simp only [middle,Fin.val_succ,Fin.val_castSucc,Fin.val_last] at hh; omega
    simp [hne]
  · simp [Fin.ext_iff]
  · have hne : Fin.last (n+1)≠middle j := by
      intro h; have hh := congrArg Fin.val h
      simp only [middle,Fin.val_succ,Fin.val_castSucc,Fin.val_last] at hh; omega
    simp [hne]
  · have he : i=j := Subsingleton.elim _ _; simp [he]
private theorem embed_middle_endpoint (g : SpecialLinearGroup (Fin n) F) (i : Fin n) :
    embed g (middle i) (0:Fin (n+2))=0 ∧ embed g (middle i) (Fin.last (n+1))=0 := by
  constructor
  · rw [← (centralKernel% index_middle) i,← centralKernel% index_first,centralKernel% entry]; rfl
  · rw [← (centralKernel% index_middle) i,← centralKernel% index_last,centralKernel% entry]; rfl
private theorem residual_middle (b : SpecialLinearGroup (Fin (n+2)) F)
    (hb : LayerDepth 1 (b.val-1)) (i j : Fin n) :
    ((embed (centralPart b hb))⁻¹*b) (middle i) (middle j)=
      (1:Matrix (Fin (n+2)) (Fin (n+2)) F) (middle i) (middle j) := by
  classical
  rw [← map_inv,SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  change embed ((centralPart b hb)⁻¹) (middle i) 0*b 0 (middle j)+
    ((∑ t : Fin n, embed ((centralPart b hb)⁻¹) (middle i) (middle t)*b (middle t) (middle j))+
      embed ((centralPart b hb)⁻¹) (middle i) (Fin.last (n+1))*b (Fin.last (n+1)) (middle j))=_
  rw [(embed_middle_endpoint _ i).1,(embed_middle_endpoint _ i).2,zero_mul,zero_mul,zero_add,add_zero]
  simp only [actual_central_levi_middle_entry]
  have he := congrArg (fun g : SpecialLinearGroup (Fin n) F => g i j)
    (inv_mul_cancel (centralPart b hb))
  simpa only [SpecialLinearGroup.coe_mul,Matrix.mul_apply,centralPart,
    Matrix.submatrix_apply,SpecialLinearGroup.coe_one,Matrix.one_apply,middle_inj.eq_iff] using he
private theorem interior (i : Fin (n+2)) (hi0 : i≠0) (hil : i≠Fin.last (n+1)) :
    ∃ j : Fin n, middle j=i := by
  have h0 : 0 < i.val := by by_contra h; apply hi0; apply Fin.ext; simp only [Fin.val_zero]; omega
  have hl : i.val < n+1 := by by_contra h; apply hil; apply Fin.ext; simp only [Fin.val_last]; omega
  refine ⟨⟨i.val-1,by omega⟩,?_⟩
  apply Fin.ext; simp only [middle,Fin.val_succ,Fin.val_castSucc]; omega
/-- The exact p255 decomposition. The middle block is constructed from
b; the true ordered group residual is proved to belong to V. -/
theorem actual_ambient_U_decomposition (b : SpecialLinearGroup (Fin (n+2)) F)
    (hb : LayerDepth 1 (b.val-1)) :
    ∃ g : SpecialLinearGroup (Fin n) F, ∃ v : SpecialLinearGroup (Fin (n+2)) F,
      LayerDepth 1 (g.val-1) ∧ InRadical v ∧ embed g*v=b := by
  let g := centralPart b hb
  let v := (embed g)⁻¹*b
  have hg := actual_central_part_unitriangular b hb
  have hvU : LayerDepth 1 (v.val-1) := (unitRec% product_depth) 1 (by omega)
    _ _ ((unitLayer% inverse_unit_depth) _ (actual_central_embed_unitriangular g hg)) hb
  refine ⟨g,v,hg,⟨hvU,?_⟩,by dsimp only [v]; group⟩
  intro i j hi hj
  by_cases hil : i=Fin.last (n+1)
  · subst i
    have he := hvU (Fin.last (n+1)) j (by simp only [Fin.val_last]; omega)
    exact sub_eq_zero.mp he
  · by_cases hj0 : j=0
    · subst j
      have he := hvU i 0 (by simp only [Fin.val_zero]; omega)
      exact sub_eq_zero.mp he
    · obtain ⟨i',rfl⟩ := interior i hi hil
      obtain ⟨j',rfl⟩ := interior j hj0 hj
      exact residual_middle b hb i' j'
end NikolovSegal.PartIIAmbientUnipotentDecomposition
