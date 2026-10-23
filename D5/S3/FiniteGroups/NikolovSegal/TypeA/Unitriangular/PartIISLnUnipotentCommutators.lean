/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnUnipotentCommutators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularProper
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnipotentBlocks

/-! An elementary type-A step toward PartII Section5 class PRODUCT width.
Every actual upper unitriangular matrix, embedded with an equally sized
auxiliary block, is a product of THREE actual commutators. The first two
solve the odd/even adjacent entries by rectangular block multiplication;
the third consumes the accepted full proper-matrix reconstruction (13).
No commutator-width, conjugacy-width, simplicity or field-size premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIISLnUnipotentCommutators
open Matrix PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- Genuine embedding with an auxiliary block of the same size. -/
def doubleEmbed : SpecialLinearGroup (Fin n) F →*
    SpecialLinearGroup (Fin n ⊕ Fin n) F where
  toFun g := ⟨fromBlocks g.val 0 0 1,by
    simp [det_fromBlocks_zero₂₁,g.prop]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [SpecialLinearGroup.coe_mul,fromBlocks_multiply])

private def upperBlock (A : Matrix (Fin n) (Fin n) F) :
    SpecialLinearGroup (Fin n ⊕ Fin n) F :=
  ⟨fromBlocks 1 A 0 1,by simp [det_fromBlocks_zero₂₁]⟩
private def lowerBlock (A : Matrix (Fin n) (Fin n) F) :
    SpecialLinearGroup (Fin n ⊕ Fin n) F :=
  ⟨fromBlocks 1 0 A 1,by simp [det_fromBlocks_zero₁₂]⟩
private theorem upper_inverse (A : Matrix (Fin n) (Fin n) F) :
    (upperBlock A)⁻¹=upperBlock (-A) := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_mul,upperBlock,fromBlocks_multiply]
private theorem lower_inverse (A : Matrix (Fin n) (Fin n) F) :
    (lowerBlock A)⁻¹=lowerBlock (-A) := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_mul,lowerBlock,fromBlocks_multiply]

private def colourDiagonal (p : ℕ) : Matrix (Fin n) (Fin n) F :=
  diagonal (fun i => if i.val%2=p then 1 else 0)
private def colourStrip (p : ℕ) (x : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  layerStrip 1 (fun i => if i.val%2=p then x i else 0)
private theorem diagonal_strip (p : ℕ) (x : Fin n → F) :
    colourDiagonal p*colourStrip p x=colourStrip p x := by
  ext i j
  simp only [colourDiagonal,colourStrip,diagonal_mul,layerStrip]
  split_ifs <;> simp_all
private theorem strip_diagonal (p : ℕ) (x : Fin n → F) :
    colourStrip p x*colourDiagonal p=0 := by
  ext i j
  simp only [colourDiagonal,colourStrip,mul_diagonal,layerStrip,Matrix.zero_apply]
  by_cases hj : j.val=i.val+1
  · by_cases hi : i.val%2=p
    · have hne : j.val%2≠p := by omega
      simp only [if_pos hj, if_pos hi, if_neg hne, mul_zero]
    · simp [hj,hi]
  · simp [hj]

/-- The two rectangular witnesses realize the complete matching strip,
including all entries, rather than just its leading coordinates. -/
private theorem matching_commutator (p : ℕ) (x : Fin n → F) :
    (upperBlock (colourDiagonal (F:=F) p))⁻¹*
      (lowerBlock (colourStrip p x))⁻¹*
      upperBlock (colourDiagonal p)*lowerBlock (colourStrip p x)=
      doubleEmbed (stripUnit 1 (by decide) (fun i => if i.val%2=p then x i else 0)) := by
  rw [upper_inverse,lower_inverse]
  apply Subtype.ext
  change (fromBlocks (1:Matrix (Fin n) (Fin n) F) (-colourDiagonal p) 0 1)*
      (fromBlocks 1 0 (-colourStrip p x) 1)*
      (fromBlocks 1 (colourDiagonal p) 0 1)*
      (fromBlocks 1 0 (colourStrip p x) 1)=
      fromBlocks (1+colourStrip p x) 0 0 1
  simp [fromBlocks_multiply,add_mul,mul_add,diagonal_strip,strip_diagonal]

private theorem unit_product (a b : SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) (hb : LayerDepth 1 (b.val-1)) :
    LayerDepth 1 ((a*b).val-1) := by
  have he : (a*b).val-1=(a.val-1)*(b.val-1)+(a.val-1)+(b.val-1) := by
    rw [SpecialLinearGroup.coe_mul]; noncomm_ring
  rw [he]
  exact (unitLayer% depth_add) ((unitLayer% depth_add)
    ((unitLayer% depth_mono) ((unitLayer% depth_mul) ha hb) (by decide)) ha) hb
private theorem strip_depth1 (x : Fin n → F) :
    LayerDepth 1 ((stripUnit 1 (by decide) x).val-1) := by
  simpa only [stripUnit,add_sub_cancel_left] using (unitLayer% strip_depth) 1 x

/-- EVERY upper unitriangular target, every field and rank (including
0/1), is reconstructed with three ordered commutators in the actual
double-sized special linear group. Witnesses depend on the target;
the auxiliary block and the number THREE do not. -/
theorem actual_upper_double_three_commutators
    (u : SpecialLinearGroup (Fin n) F) (hu : LayerDepth 1 (u.val-1)) :
    ∃ a b : Fin 3 → SpecialLinearGroup (Fin n ⊕ Fin n) F,
      (List.ofFn (fun i => (a i)⁻¹*(b i)⁻¹*a i*b i)).prod=doubleEmbed u := by
  classical
  let x : Fin n → F := fun i => if hi : i.val+1<n then u i ⟨i.val+1,hi⟩ else 0
  let w0 := stripUnit 1 (by decide) (fun i => if i.val%2=0 then x i else 0)
  let w1 := stripUnit 1 (by decide) (fun i => if i.val%2=1 then x i else 0)
  have hw0 : LayerDepth 1 (w0.val-1) := strip_depth1 _
  have hw1 : LayerDepth 1 (w1.val-1) := strip_depth1 _
  let w := w0*w1
  have hw : LayerDepth 1 (w.val-1) := unit_product _ _ hw0 hw1
  let v := w⁻¹*u
  have hv1 : LayerDepth 1 (v.val-1) :=
    unit_product _ _ ((unitLayer% inverse_unit_depth) w hw) hu
  have hfirst : ∀ i : ℕ, ∀ hi : i+1<n, w ⟨i,by omega⟩ ⟨i+1,hi⟩=
      u ⟨i,by omega⟩ ⟨i+1,hi⟩ := by
    intro i hi
    rw [(unitAction% adjacent_product) w0 w1 hw0 hw1 i hi]
    have hne : (⟨i,by omega⟩ : Fin n)≠⟨i+1,hi⟩ := by
      intro h; have hh := congrArg Fin.val h; change i=i+1 at hh; omega
    change (1+layerStrip 1 (fun j => if j.val%2=0 then x j else 0)) ⟨i,by omega⟩ ⟨i+1,hi⟩+
      (1+layerStrip 1 (fun j => if j.val%2=1 then x j else 0)) ⟨i,by omega⟩ ⟨i+1,hi⟩=_
    simp only [Matrix.add_apply,Matrix.one_apply,if_neg hne,zero_add,layerStrip,
      Fin.val_mk,ite_true,x,dif_pos hi]
    by_cases hp : i%2=0
    · simp [hp]
    · have hp' : i%2=1 := by omega
      simp [hp,hp']
  have hv : LayerDepth 2 (v.val-1) := by
    intro i j hij
    by_cases h : j.val < i.val+1
    · exact hv1 i j h
    · have he : j.val=i.val+1 := by omega
      have hne : i≠j := by intro hh; subst j; omega
      have hh := (unitAction% adjacent_product) w⁻¹ u
        ((unitLayer% inverse_unit_depth) w hw) hu i.val (by omega)
      have hj : (⟨i.val+1,by omega⟩ : Fin n)=j := Fin.ext he.symm
      rw [(unitAction% adjacent_inverse) w hw,hfirst] at hh
      simpa only [v,Matrix.sub_apply,Matrix.one_apply,if_neg hne,sub_zero,hj,
        neg_add_cancel] using hh
  let g := stripUnit 1 (by decide) (fun _ : Fin n => (1:F))
  have hg : LayerDepth 1 (g.val-1) := strip_depth1 _
  have hproper : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩≠0 := by
    intro i hi
    have hne : (⟨i,by omega⟩ : Fin n)≠⟨i+1,hi⟩ := by
      intro h; have hh := congrArg Fin.val h; change i=i+1 at hh; omega
    simp [g,stripUnit,layerStrip,hne]
  obtain ⟨z,hz,hzv⟩ := PartIIUnitriangularReconstruction.actual_proper_commutator_layer_reconstruction
    1 (by decide) g hg hproper v hv
  let a : Fin 3 → SpecialLinearGroup (Fin n ⊕ Fin n) F :=
    ![upperBlock (colourDiagonal 0),upperBlock (colourDiagonal 1),doubleEmbed z]
  let b : Fin 3 → SpecialLinearGroup (Fin n ⊕ Fin n) F :=
    ![lowerBlock (colourStrip 0 x),lowerBlock (colourStrip 1 x),doubleEmbed g]
  refine ⟨a,b,?_⟩
  have h0 := matching_commutator 0 x
  have h1 := matching_commutator 1 x
  have h2 : (doubleEmbed z)⁻¹*(doubleEmbed g)⁻¹*doubleEmbed z*doubleEmbed g=doubleEmbed v := by
    rw [← map_inv,← map_inv,← map_mul,← map_mul,← map_mul,hzv]
  simp only [a,b,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.succ_zero_eq_one,mul_one]
  rw [h0,h1,h2,← map_mul,← map_mul]
  congr 1
  change w0*(w1*((w0*w1)⁻¹*u))=u
  group
end NikolovSegal.PartIISLnUnipotentCommutators
