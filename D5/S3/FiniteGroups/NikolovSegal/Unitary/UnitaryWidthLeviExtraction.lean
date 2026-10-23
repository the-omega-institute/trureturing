/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthLeviExtraction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthLeviExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthLeviGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! Genuine central SU(n-2) extraction from literal endpoint equations.
The middle determinant comes from two triangular block determinants;
Steinberg fixedness of both factors follows from uniqueness of the middle block. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow PartIIUnitaryUpperTorus PartIIUnitaryLeviDecomposition
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

private abbrev blockIndex : Fin 1 ⊕ (Fin n ⊕ Fin 1) ≃ Fin (n+2) := centralKernel% indexEquiv
private theorem blockIndex_left (i : Fin 1) : blockIndex (n:=n) (Sum.inl i)=leftEnd := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact centralKernel% index_first
private theorem blockIndex_mid (i : Fin n) : blockIndex (Sum.inr (Sum.inl i))=mid i :=
  (centralKernel% index_middle) i
private theorem blockIndex_right (i : Fin 1) : blockIndex (n:=n) (Sum.inr (Sum.inr i))=rightEnd := by
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact centralKernel% index_last

/-- Actual determinant of the constructed principal block, including empty blocks. -/
theorem endpoint_middle_det (g : SpecialLinearGroup (Fin (n+2)) F) (hg : Endpoints g) :
    (g.val.submatrix mid mid).det=1 := by
  classical
  have h1 : ∀ i : Fin 1, i=0 := fun i => Subsingleton.elim _ _
  let B := g.val.submatrix mid mid
  let R : Matrix (Fin 1) (Fin n ⊕ Fin 1) F :=
    fun _ j => g.val leftEnd (blockIndex (Sum.inr j))
  let C : Matrix (Fin n) (Fin 1) F := fun i _ => g.val (mid i) rightEnd
  have hshape : g.val.submatrix blockIndex blockIndex=
      fromBlocks (1:Matrix (Fin 1) (Fin 1) F) R 0
        (fromBlocks B C 0 (1:Matrix (Fin 1) (Fin 1) F)) := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j)
    all_goals simp [Matrix.submatrix_apply,blockIndex_left,blockIndex_mid,blockIndex_right,
      Matrix.fromBlocks,R,C,B,hg.1,hg.2,Matrix.one_apply,mid_ne_left,mid_ne_right,
      left_ne_right,h1,Ne.symm (mid_ne_right _)]
  have hd : (g.val.submatrix blockIndex blockIndex).det=1 := by
    rw [Matrix.det_submatrix_equiv_self,g.prop]
  rw [hshape,Matrix.det_fromBlocks_zero₂₁,Matrix.det_fromBlocks_zero₂₁] at hd
  simpa [B] using hd

/-- Complete actual endpoint-stabilizer decomposition. No Levi, determinant,
unitarity, or decomposition input is supplied for the constructed factors. -/
theorem endpoint_levi_radical (g : specialUnitary (n+2) ι) (hg : Endpoints g.val) :
    ∃ b : specialUnitary n ι, ∃ v : specialUnitary (n+2) ι,
      UpRadical v ∧ centralEmbed b*v=g := by
  let B : SpecialLinearGroup (Fin n) F := ⟨g.val.val.submatrix mid mid,endpoint_middle_det g.val hg⟩
  let v : SpecialLinearGroup (Fin (n+2)) F := (PartIICentralLevi.embed B)⁻¹*g.val
  have hE := slCentral_endpoints B
  have hvE : Endpoints v := endpoints_mul (endpoints_inv hE) hg
  have hvM : v.val.submatrix mid mid=(1:Matrix (Fin n) (Fin n) F) := by
    rw [middle_product (endpoints_inv hE) hg]
    rw [← map_inv,slCentral_middle]
    change (B⁻¹).val*B.val=_
    exact congrArg Subtype.val (inv_mul_cancel B)
  have hv := slRadical_of_endpoints_middle hvE hvM
  have hgv : PartIICentralLevi.embed B*v=g.val := by dsimp only [v]; group
  have he : PartIICentralLevi.embed (steinberg ι B)*steinberg ι v=
      PartIICentralLevi.embed B*v := by
    rw [← actual_steinberg_central_levi,← map_mul,hgv,g.prop]
  have hvS := actual_steinberg_radical_mem ι v hv
  have hB : steinberg ι B=B := by
    apply SpecialLinearGroup.ext
    intro i j
    have hh := congrArg (fun A : SpecialLinearGroup (Fin (n+2)) F => A (mid i) (mid j)) he
    simpa only [actual_levi_radical_middle _ _ hvS,actual_levi_radical_middle _ _ hv] using hh
  have hV : steinberg ι v=v := by
    rw [hB] at he
    exact mul_left_cancel he
  refine ⟨⟨B,hB⟩,⟨v,hV⟩,hv,?_⟩
  exact Subtype.ext hgv

end NikolovSegal.UnitaryWholeGroupWidth
