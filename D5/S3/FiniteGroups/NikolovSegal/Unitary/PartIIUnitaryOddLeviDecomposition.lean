/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddLeviDecomposition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddLeviDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryOddPPrescribed
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII Definition6.8, p255 and pp271–272: the actual odd-dimensional
U2 Levi and U=U2 P. All three blocks and the P constraint are derived
from the actual upper/unitary target, including characteristic two. -/
namespace NikolovSegal.PartIIUnitaryOddLeviDecomposition
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIUnitaryUpperTorus PartIIUnitaryOddP UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}
private abbrev label : (Fin d ⊕ (Unit ⊕ Fin d)) ≃ Fin (2*d+1) := oddP% label
private def left (i : Fin d) : Fin (2*d+1) := label (.inl i)
private def mid : Fin (2*d+1) := label (.inr (.inl ()))
private def right (i : Fin d) : Fin (2*d+1) := label (.inr (.inr i))
private theorem swap_left (i : Fin d) : (oddP% swap) (.inl i)=.inr (.inr i) := rfl
private theorem swap_mid (i : Unit) : (oddP% swap) (.inr (.inl i) : Fin d ⊕ (Unit ⊕ Fin d))=.inr (.inl i) := rfl
private theorem swap_right (i : Fin d) : (oddP% swap) (.inr (.inr i))=.inl i := rfl
private theorem left_inj : Function.Injective (left : Fin d → Fin (2*d+1)) :=
  label.injective.comp Sum.inl_injective
private def lower (ι : RingAut F) (g : SpecialLinearGroup (Fin d) F) : SpecialLinearGroup (Fin d) F := (unitaryTypeA% lower) ι g
private theorem lower_entry (ι : RingAut F) (g : SpecialLinearGroup (Fin d) F) (i j : Fin d) :
    lower ι g i j=ι (g⁻¹ j i) := rfl
private theorem lower_mul (ι : RingAut F) (g h : SpecialLinearGroup (Fin d) F) :
    lower ι (g*h)=lower ι g*lower ι h := (unitaryTypeA% lower_mul) ι g h
private theorem lower_one (ι : RingAut F) : lower (d:=d) ι 1=1 := by
  apply SpecialLinearGroup.ext; intro i j
  simp [lower_entry,Matrix.one_apply,eq_comm]
private def rawEmbed (ι : RingAut F) : SpecialLinearGroup (Fin d) F →*
    SpecialLinearGroup (Fin d ⊕ (Unit ⊕ Fin d)) F where
  toFun g := ⟨fromBlocks g.val 0 0 (fromBlocks 1 0 0 (lower ι g).val),by
    simp [det_fromBlocks_zero₂₁,g.prop,(lower ι g).prop]⟩
  map_one' := by apply Subtype.ext; simp [lower_one,fromBlocks_one]
  map_mul' g h := by
    apply Subtype.ext
    simp [lower_mul,SpecialLinearGroup.coe_mul,fromBlocks_multiply]
def embed (ι : RingAut F) : SpecialLinearGroup (Fin d) F →*
    SpecialLinearGroup (Fin (2*d+1)) F :=
  (SLnUnipotentWidth.reindexSL label).toMonoidHom.comp (rawEmbed ι)
theorem actual_odd_levi_entry (ι : RingAut F) (g : SpecialLinearGroup (Fin d) F)
    (i j : Fin d ⊕ (Unit ⊕ Fin d)) :
    embed ι g (label i) (label j)=
      fromBlocks g.val 0 0 (fromBlocks 1 0 0 (lower ι g).val) i j := by
  simp [embed,SLnUnipotentWidth.reindexSL,rawEmbed,Matrix.reindex_apply,Matrix.submatrix_apply]
theorem actual_odd_levi_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin d) F) : steinberg ι (embed ι g)=embed ι g := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := label.surjective i
  obtain ⟨j,rfl⟩ := label.surjective j
  rw [steinberg_entry,← map_inv,← oddP% label_reflection,← oddP% label_reflection,
    actual_odd_levi_entry,actual_odd_levi_entry]
  cases i with
  | inl i => cases j with
    | inl j => simpa only [swap_left,swap_mid,swap_right,fromBlocks_apply₁₁,fromBlocks_apply₂₂,lower_entry,inv_inv] using hinv (g i j)
    | inr j => cases j <;> simp [swap_left,swap_mid,swap_right]
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp [swap_left,swap_mid,swap_right]
      | inr j => cases j <;> simp [swap_left,swap_mid,swap_right,Matrix.one_apply]
    | inr i => cases j with
      | inl j => simp [swap_left,swap_mid,swap_right]
      | inr j => cases j <;> simp [swap_left,swap_mid,swap_right,lower_entry]
theorem actual_odd_levi_upper (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin d) F) (hg : LayerDepth 1 (g.val-1)) :
    LayerDepth 1 ((embed ι g).val-1) := by
  have hgi := (unitLayer% inverse_unit_depth) g hg
  intro i j hij
  obtain ⟨i,rfl⟩ := label.surjective i
  obtain ⟨j,rfl⟩ := label.surjective j
  simp only [Matrix.sub_apply,actual_odd_levi_entry,Matrix.one_apply,label.injective.eq_iff]
  cases i with
  | inl i => cases j with
    | inl j =>
      have hh := hg i j (by change j.val < i.val+1 at hij; exact hij)
      simpa only [fromBlocks_apply₁₁,Matrix.sub_apply,Matrix.one_apply,Sum.inl.injEq] using hh
    | inr j => simp
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp
      | inr j => cases j <;> simp [Matrix.one_apply]
    | inr i => cases j with
      | inl j => simp
      | inr j => cases j with
        | inl j => simp
        | inr j =>
          have hji : i.val < j.val+1 := by change 2*d-j.val < 2*d-i.val+1 at hij; have hi:=i.isLt; have hj:=j.isLt; omega
          have he := sub_eq_zero.mp (hgi j i hji)
          simp only [fromBlocks_apply₂₂,lower_entry,he,Matrix.one_apply,Sum.inr.injEq]
          simp [Matrix.one_apply,eq_comm]
private theorem upper_zero (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (i j : Fin (2*d+1)) (hij : j.val < i.val) : b i j=0 := by
  have hne : i≠j := fun he => by subst j; omega
  simpa only [Matrix.sub_apply,Matrix.one_apply,if_neg hne,sub_zero] using hb i j (by omega)
private theorem upper_diag (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (i : Fin (2*d+1)) : b i i=1 := by
  exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true] using hb i i (by omega))
private theorem mid_left_zero (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (j : Fin d) : b mid (left j)=0 :=
  upper_zero b hb _ _ (by change j.val < d; exact j.isLt)
private theorem right_left_zero (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (i j : Fin d) : b (right i) (left j)=0 :=
  upper_zero b hb _ _ (by change j.val < 2*d-i.val; have hi:=i.isLt; have hj:=j.isLt; omega)
private theorem right_mid_zero (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (i : Fin d) : b (right i) mid=0 :=
  upper_zero b hb _ _ (by change d < 2*d-i.val; have hi:=i.isLt; omega)
private theorem top_mul (a b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (i j : Fin d) :
    (a*b) (left i) (left j)=∑ t : Fin d, a (left i) (left t)*b (left t) (left j) := by
  rw [SpecialLinearGroup.coe_mul,Matrix.mul_apply,← label.sum_comp,Fintype.sum_sum_type,Fintype.sum_sum_type]
  change (∑ t : Fin d, a (left i) (left t)*b (left t) (left j))+
    ((∑ t : Unit, a (left i) mid*b mid (left j))+
      (∑ t : Fin d, a (left i) (right t)*b (right t) (left j)))=_
  simp only [mid_left_zero b hb,right_left_zero b hb,mul_zero,Finset.sum_const_zero,add_zero]
private def top (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) : SpecialLinearGroup (Fin d) F :=
  ⟨b.val.submatrix left left,by
    have ht : IsUpperTriangular (b.val.submatrix left left) := by
      intro i j hij
      exact upper_zero b hb _ _ (by change j.val < i.val; exact hij)
    rw [det_of_isUpperTriangular ht]
    exact Finset.prod_eq_one (fun i _ => upper_diag b hb (left i))⟩
private theorem top_upper (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) : LayerDepth 1 ((top b hb).val-1) := by
  intro i j hij
  have hinj : Function.Injective (left : Fin d → Fin (2*d+1)) := label.injective.comp Sum.inl_injective
  simpa only [top,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.one_apply,hinj.eq_iff]
    using hb (left i) (left j) (by change j.val < i.val+1; exact hij)
private theorem residual_top (b : SpecialLinearGroup (Fin (2*d+1)) F)
    (hb : LayerDepth 1 (b.val-1)) (ι : RingAut F) (i j : Fin d) :
    ((embed ι (top b hb))⁻¹*b) (left i) (left j)=(1:Matrix (Fin d) (Fin d) F) i j := by
  rw [← map_inv,top_mul _ _ hb]
  have he := congrArg (fun g : SpecialLinearGroup (Fin d) F => g i j) (inv_mul_cancel (top b hb))
  simpa only [left,actual_odd_levi_entry,fromBlocks_apply₁₁,top,Matrix.submatrix_apply,
    SpecialLinearGroup.coe_mul,Matrix.mul_apply,SpecialLinearGroup.coe_one] using he

/-- Actual odd U=U2 P, with genuine vector/central constraints constructed
from every actual target; no decomposition or coordinate-law input. -/
theorem actual_odd_unitary_U_decomposition (ι : RingAut F) (hinv : Function.Involutive ι)
    (b : SpecialLinearGroup (Fin (2*d+1)) F) (hb : LayerDepth 1 (b.val-1))
    (hbu : steinberg ι b=b) :
    ∃ g : SpecialLinearGroup (Fin d) F, ∃ v : Fin d → F, ∃ B : Matrix (Fin d) (Fin d) F,
      LayerDepth 1 (g.val-1) ∧ Constraint ι v B ∧ embed ι g*p ι v B=b := by
  let g := top b hb
  let r := (embed ι g)⁻¹*b
  have hg := top_upper b hb
  have hr : LayerDepth 1 (r.val-1) := (unitRec% product_depth) 1 (by omega) _ _
    ((unitLayer% inverse_unit_depth) _ (actual_odd_levi_upper ι hinv g hg)) hb
  have hru : steinberg ι r=r := by
    dsimp only [r]; rw [map_mul,map_inv,actual_odd_levi_unitary ι hinv,hbu]
  have htop : ∀ i j : Fin d, r (left i) (left j)=(1:Matrix (Fin d) (Fin d) F) i j :=
    residual_top b hb ι
  have hri := (unitLayer% inverse_unit_depth) r hr
  have hitop : ∀ i j : Fin d, r⁻¹ (left i) (left j)=(1:Matrix (Fin d) (Fin d) F) i j := by
    intro i j
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d+1)) F => a (left i) (left j)) (mul_inv_cancel r)
    rw [top_mul _ _ hri] at hh
    simpa only [htop,Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true,SpecialLinearGroup.coe_one,left_inj.eq_iff] using hh
  have hbot : ∀ i j : Fin d, r (right i) (right j)=(1:Matrix (Fin d) (Fin d) F) i j := by
    intro i j
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d+1)) F => a (right i) (right j)) hru
    rw [steinberg_entry] at hh
    have hi : (right i).rev=left i := (oddP% label_reflection) (.inr (.inr i)) |>.symm
    have hj : (right j).rev=left j := (oddP% label_reflection) (.inr (.inr j)) |>.symm
    rw [hi,hj,hitop] at hh
    simpa only [Matrix.one_apply,eq_comm,apply_ite,map_one,map_zero] using hh.symm
  let v : Fin d → F := fun i => r (left i) mid
  let B : Matrix (Fin d) (Fin d) F := fun i j => r (left i) (right j)
  have himid : ∀ i : Fin d, r⁻¹ (left i) mid= -v i := by
    intro i
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d+1)) F => a (left i) mid) (mul_inv_cancel r)
    rw [SpecialLinearGroup.coe_mul,Matrix.mul_apply,← label.sum_comp,Fintype.sum_sum_type,Fintype.sum_sum_type] at hh
    change (∑ t : Fin d, r (left i) (left t)*r⁻¹ (left t) mid)+
      ((∑ t : Unit, r (left i) mid*r⁻¹ mid mid)+
        (∑ t : Fin d, r (left i) (right t)*r⁻¹ (right t) mid))=_ at hh
    have hne : left i≠mid := by intro he; have he':=label.injective he; cases he'
    simp only [htop,Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,
      ite_true,upper_diag _ hri,right_mid_zero _ hri,mul_zero,Finset.sum_const_zero,mul_one,
      Fintype.sum_unique,add_zero,SpecialLinearGroup.coe_one,if_neg hne] at hh
    dsimp only [v]
    linear_combination hh
  have hrow : ∀ j : Fin d, r mid (right j)= -ι (v j) := by
    intro j
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d+1)) F => a mid (right j)) hru
    rw [steinberg_entry] at hh
    have hj : (right j).rev=left j := (oddP% label_reflection) (.inr (.inr j)) |>.symm
    have hm : (mid : Fin (2*d+1)).rev=mid := (oddP% label_reflection) (.inr (.inl ())) |>.symm
    rw [hj,hm,himid,map_neg] at hh
    exact hh.symm
  have hrP : r=p ι v B := by
    apply SpecialLinearGroup.ext
    intro i j
    obtain ⟨i,rfl⟩ := label.surjective i
    obtain ⟨j,rfl⟩ := label.surjective j
    rw [actual_p_entry]
    cases i with
    | inl i => cases j with
      | inl j => exact htop i j
      | inr j => cases j <;> rfl
    | inr i => cases i with
      | inl i => cases i; cases j with
        | inl j => exact mid_left_zero r hr j
        | inr j => cases j with
          | inl j => cases j; exact upper_diag r hr mid
          | inr j => exact hrow j
      | inr i => cases j with
        | inl j => exact right_left_zero r hr i j
        | inr j => cases j with
          | inl j => cases j; exact right_mid_zero r hr i
          | inr j => exact hbot i j
  refine ⟨g,v,B,hg,(actual_p_unitary_iff ι hinv v B).mp ?_,?_⟩
  · rw [← hrP]; exact hru
  · rw [← hrP]; dsimp only [r]; group
theorem actual_odd_levi_field_action (ι phi : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (g : SpecialLinearGroup (Fin d) F) :
    fieldAut phi (embed ι g)=embed ι (fieldAut phi g) := by
  have hcomm : ∀ x : F, phi (ι x)=ι (phi x) := by
    intro x
    rw [involution_eq_pow ι hinv hne x,map_pow,involution_eq_pow ι hinv hne (phi x)]
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := label.surjective i
  obtain ⟨j,rfl⟩ := label.surjective j
  change phi (embed ι g (label i) (label j))=_
  rw [actual_odd_levi_entry,actual_odd_levi_entry]
  cases i with
  | inl i => cases j with
    | inl j => rfl
    | inr j => exact map_zero phi
  | inr i => cases i with
    | inl i => cases j with
      | inl j => exact map_zero phi
      | inr j => cases j with
        | inl j => simp [Matrix.one_apply]
        | inr j => exact map_zero phi
    | inr i => cases j with
      | inl j => exact map_zero phi
      | inr j => cases j with
        | inl j => exact map_zero phi
        | inr j =>
          simp only [fromBlocks_apply₂₂,lower_entry,← map_inv]
          exact hcomm (g⁻¹ j i)
private def pairedWeights (ι : RingAut F) (eta : Fin d → Fˣ) : Fin (2*d+1) → Fˣ :=
  fun i => Sum.elim eta (Sum.elim (fun _ => 1) (fun j => (involutionUnit ι (eta j))⁻¹)) (label.symm i)
private theorem pairedWeights_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (eta : Fin d → Fˣ) (i : Fin (2*d+1)) :
    ι (pairedWeights ι eta i:F)*(pairedWeights ι eta i.rev:F)=1 := by
  obtain ⟨i,rfl⟩ := label.surjective i
  rw [← oddP% label_reflection]
  cases i with
  | inl i => simp [swap_left,swap_mid,swap_right,pairedWeights,involutionUnit_val,Units.val_inv_eq_inv_val]
  | inr i => cases i with
    | inl i => simp [swap_left,swap_mid,swap_right,pairedWeights]
    | inr i => simp [swap_left,swap_mid,swap_right,pairedWeights,involutionUnit_val,Units.val_inv_eq_inv_val,map_inv₀,hinv (eta i:F)]
private theorem paired_diagonal_action (ι : RingAut F) (eta : Fin d → Fˣ)
    (g : SpecialLinearGroup (Fin d) F) :
    (unitOdd% diagonalAut) (pairedWeights ι eta) (embed ι g)=
      embed ι ((unitOdd% diagonalAut) eta g) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := label.surjective i
  obtain ⟨j,rfl⟩ := label.surjective j
  rw [unitOdd% diagonal_entry,actual_odd_levi_entry,actual_odd_levi_entry]
  cases i with
  | inl i => cases j with
    | inl j => simp [swap_left,swap_mid,swap_right,pairedWeights,unitOdd% diagonal_entry]
    | inr j => simp
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp
      | inr j => cases j <;> simp [swap_left,swap_mid,swap_right,pairedWeights,Matrix.one_apply]
    | inr i => cases j with
      | inl j => simp
      | inr j => cases j with
        | inl j => simp
        | inr j =>
          simp only [fromBlocks_apply₂₂,lower_entry,← map_inv]
          rw [unitOdd% diagonal_entry]
          simp only [pairedWeights,Equiv.symm_apply_apply,Sum.elim_inr,involutionUnit_val,
            inv_inv,Units.val_inv_eq_inv_val,map_mul,map_inv₀]
          ring
/-- Actual ambient determinant-one unitary H realizes every diagonal
action on the odd type-A Levi, before any group target. -/
theorem actual_odd_levi_ambient_diagonal_inner (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F) (eta : Fin d → Fˣ) :
    ∃ h : SpecialLinearGroup (Fin (2*d+1+2)) F,
      steinberg ι h=h ∧ ∀ g : SpecialLinearGroup (Fin d) F,
        (MulAut.conj h) (PartIICentralLevi.embed (embed ι g))=
          PartIICentralLevi.embed (embed ι ((unitOdd% diagonalAut) eta g)) := by
  obtain ⟨h,_,hhu,hcover⟩ := PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
    ι hinv hne (pairedWeights ι eta) 1 (pairedWeights_unitary ι hinv eta)
  refine ⟨h,hhu,?_⟩
  intro g
  rw [hcover,paired_diagonal_action]
end NikolovSegal.PartIIUnitaryOddLeviDecomposition
