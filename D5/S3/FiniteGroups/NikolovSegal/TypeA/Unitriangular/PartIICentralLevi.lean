/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIRadicalInnerTorus
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnipotentBlocks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Part II p255: actual central SL(n-2), with full diagonal actions
implemented by determinant-one ambient inner corrections. -/
namespace NikolovSegal.PartIICentralLevi
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
universe u
variable {F : Type u} [Field F] {n : ℕ}
private def indexEquiv : Fin 1 ⊕ (Fin n ⊕ Fin 1) ≃ Fin (n+2) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))
def middle (i : Fin n) : Fin (n+2) := i.castSucc.succ
private theorem index_middle (i : Fin n) : indexEquiv (Sum.inr (Sum.inl i))=middle i := by
  apply Fin.ext; change 1+i.val=i.val+1; omega
private theorem index_first : indexEquiv (Sum.inl (0:Fin 1))=(0:Fin (n+2)) := by
  apply Fin.ext; rfl
private theorem index_last : indexEquiv (Sum.inr (Sum.inr (0:Fin 1)))=Fin.last (n+1) := by
  apply Fin.ext; change 1+(n+0)=n+1; omega
private def blockEmbed : SpecialLinearGroup (Fin n) F →*
    SpecialLinearGroup (Fin 1 ⊕ (Fin n ⊕ Fin 1)) F where
  toFun g := ⟨fromBlocks 1 0 0 (SLnUnipotentWidth.embed g).val,by
    simp [det_fromBlocks_zero₂₁,(SLnUnipotentWidth.embed g).prop]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [SpecialLinearGroup.coe_mul,fromBlocks_multiply])
/-- The genuine central Levi embedding, fixing the first and last factors. -/
def embed : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin (n+2)) F :=
  (SLnUnipotentWidth.reindexSL indexEquiv).toMonoidHom.comp blockEmbed
private theorem entry (g : SpecialLinearGroup (Fin n) F)
    (i j : Fin 1 ⊕ (Fin n ⊕ Fin 1)) :
    embed g (indexEquiv i) (indexEquiv j)=
      fromBlocks (1:Matrix (Fin 1) (Fin 1) F) 0 0 (fromBlocks g.val 0 0 (1:Matrix (Fin 1) (Fin 1) F)) i j := by
  simp [embed,SLnUnipotentWidth.reindexSL,blockEmbed,SLnUnipotentWidth.embed,
    Matrix.reindex_apply,Matrix.submatrix_apply]
theorem actual_central_levi_middle_entry (g : SpecialLinearGroup (Fin n) F) (i j : Fin n) :
    embed g (middle i) (middle j)=g i j := by
  rw [← index_middle i,← index_middle j,entry]; rfl
private theorem rev_middle (i : Fin n) : (middle i).rev=middle i.rev := by
  apply Fin.ext; simp only [middle,Fin.val_rev,Fin.val_succ,Fin.val_castSucc]; omega
private def blockReverse : Fin 1 ⊕ (Fin n ⊕ Fin 1) → Fin 1 ⊕ (Fin n ⊕ Fin 1)
  | Sum.inl _ => Sum.inr (Sum.inr 0)
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i.rev)
  | Sum.inr (Sum.inr _) => Sum.inl 0
private theorem reverse_index (i : Fin 1 ⊕ (Fin n ⊕ Fin 1)) :
    (indexEquiv i).rev=indexEquiv (blockReverse i) := by
  rcases i with i | (i | i)
  · have hi : i=0 := Subsingleton.elim _ _; subst i
    simp only [blockReverse]
    rw [index_first,index_last]; apply Fin.ext; simp [Fin.val_rev]
  · simpa only [blockReverse,index_middle] using rev_middle i
  · have hi : i=0 := Subsingleton.elim _ _; subst i
    simp only [blockReverse]
    rw [index_last,index_first]; apply Fin.ext; simp [Fin.val_rev]
private theorem field_embed (phi : RingAut F) (g : SpecialLinearGroup (Fin n) F) :
    fieldAut phi (embed g)=embed (fieldAut phi g) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := indexEquiv.surjective i
  obtain ⟨j,rfl⟩ := indexEquiv.surjective j
  change phi (embed g (indexEquiv i) (indexEquiv j))=_
  rw [entry,entry]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp [Matrix.fromBlocks,Matrix.one_apply,fieldAut]
private theorem raw_graph_embed (g : SpecialLinearGroup (Fin n) F) :
    (unitAction% rawGraph) (embed g)=embed ((unitAction% rawGraph) g) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := indexEquiv.surjective i
  obtain ⟨j,rfl⟩ := indexEquiv.surjective j
  rw [(unitAction% rawGraph_entry),reverse_index,reverse_index,← map_inv,entry,entry]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp [blockReverse,Matrix.fromBlocks,Matrix.one_apply,unitAction% rawGraph_entry]
  all_goals exact Subsingleton.elim _ _
private theorem torus_embed (lambda : Fˣ) (g : SpecialLinearGroup (Fin n) F) :
    heightTorus lambda (embed g)=embed (heightTorus lambda g) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := indexEquiv.surjective i
  obtain ⟨j,rfl⟩ := indexEquiv.surjective j
  rw [(unitAction% torus_entry),entry,entry]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals try { simp [Matrix.fromBlocks,Matrix.one_apply] }
  · have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j; simp [index_first,Matrix.fromBlocks,Matrix.one_apply]
  · simp only [Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₁,index_middle,middle,
      Fin.val_succ,Fin.val_castSucc,(unitAction% torus_entry),pow_succ]
    have hl : (((lambda⁻¹:Fˣ):F):F)*(lambda:F)=1 := by simp
    calc
      _ = (((lambda⁻¹:Fˣ):F)^i.val*g i j*(lambda:F)^j.val)*
        ((((lambda⁻¹:Fˣ):F):F)*(lambda:F)) := by ring
      _ = _ := by rw [hl,mul_one]
  · have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    simp only [Matrix.fromBlocks_apply₂₂,Matrix.one_apply,ite_true,mul_one]
    rw [← mul_pow]; simp
private theorem field_graph_embed (phi : RingAut F) (eps : Bool)
    (g : SpecialLinearGroup (Fin n) F) : fieldGraphAut phi eps (embed g)=embed (fieldGraphAut phi eps g) := by
  cases eps
  · exact field_embed phi g
  · change fieldAut phi (heightTorus (-1:Fˣ) ((unitAction% rawGraph) (embed g)))=_
    rw [raw_graph_embed,torus_embed,field_embed]; rfl
private theorem diagonal_embed (a : Fin (n+2) → Fˣ) (g : SpecialLinearGroup (Fin n) F) :
    (unitOdd% diagonalAut) a (embed g)=embed ((unitOdd% diagonalAut) (fun i => a (middle i)) g) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := indexEquiv.surjective i
  obtain ⟨j,rfl⟩ := indexEquiv.surjective j
  rw [(unitOdd% diagonal_entry),entry,entry]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals try { simp [Matrix.fromBlocks,Matrix.one_apply] }
  · have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j; simp [Matrix.fromBlocks,Matrix.one_apply]
  · simp only [Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₁,index_middle,(unitOdd% diagonal_entry)]
  · have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j; simp [Matrix.fromBlocks,Matrix.one_apply]
/-- Full actual ambient field/graph/diagonal action intertwines with the
central action, including inverse-transpose and its signs. -/
theorem actual_central_levi_action (a : Fin (n+2) → Fˣ) (phi : RingAut F) (eps : Bool)
    (g : SpecialLinearGroup (Fin n) F) :
    PartIIProposition6_5.diagonalFieldGraph a phi eps (embed g)=
      embed (PartIIProposition6_5.diagonalFieldGraph (fun i => a (middle i)) phi eps g) := by
  change (unitOdd% diagonalAut) a (fieldGraphAut phi eps (embed g))=_
  rw [field_graph_embed,diagonal_embed]; rfl
end NikolovSegal.PartIICentralLevi
