/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenP
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenP
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTypeALeviProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-! Part II Definition6.8, p255 and Proposition6.10, pp271–272.
For even SU dimension the actual P is an abelian upper-right block.
Its skew-Hermitian constraint and ordered U=U2 P factorization are
DERIVED from the actual Steinberg action, including characteristic two. -/
namespace NikolovSegal.PartIIUnitaryEvenP
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIUnitaryUpperTorus PartIIUnitaryTypeALevi PartIIUnitaryTorusSupply
open UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}

private def left (i : Fin d) : Fin (2*d) := evenLabel d (.inl i)
private def right (i : Fin d) : Fin (2*d) := evenLabel d (.inr i)
private theorem left_val (i : Fin d) : (left i).val=i.val := rfl
private theorem right_val (i : Fin d) : (right i).val=d+(d-(i.val+1)) := rfl
private theorem left_inj : Function.Injective (left : Fin d → Fin (2*d)) :=
  (evenLabel d).injective.comp Sum.inl_injective
private theorem right_inj : Function.Injective (right : Fin d → Fin (2*d)) :=
  (evenLabel d).injective.comp Sum.inr_injective
private theorem right_ne_left (i j : Fin d) : right i≠left j := by
  intro he
  have hh := (evenLabel d).injective he
  cases hh
private theorem rev_left (i : Fin d) : (left i).rev=right i :=
  (evenLabel_reflection d (.inl i)).symm
private theorem rev_right (i : Fin d) : (right i).rev=left i :=
  (evenLabel_reflection d (.inr i)).symm

private def pairP (B : Matrix (Fin d) (Fin d) F) :
    SpecialLinearGroup (Fin d⊕Fin d) F :=
  ⟨fromBlocks 1 B 0 1,by simp [det_fromBlocks_zero₂₁]⟩
/-- Actual positive P element in the native anti-diagonal coordinates. -/
def p (B : Matrix (Fin d) (Fin d) F) : SpecialLinearGroup (Fin (2*d)) F :=
  SLnUnipotentWidth.reindexSL (evenLabel d) (pairP B)

theorem actual_p_entry (B : Matrix (Fin d) (Fin d) F) (i j : Fin d⊕Fin d) :
    p B (evenLabel d i) (evenLabel d j)=fromBlocks 1 B 0 1 i j := by
  simp [p,SLnUnipotentWidth.reindexSL,pairP,Matrix.reindex_apply,Matrix.submatrix_apply]

theorem actual_p_add (B C : Matrix (Fin d) (Fin d) F) : p (B+C)=p B*p C := by
  unfold p
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp [pairP,SpecialLinearGroup.coe_mul,fromBlocks_multiply,add_comm]
private theorem p_zero : p (0:Matrix (Fin d) (Fin d) F)=1 := by
  unfold p
  rw [show pairP (0:Matrix (Fin d) (Fin d) F)=1 by apply Subtype.ext; exact fromBlocks_one]
  exact map_one _
theorem actual_p_inverse (B : Matrix (Fin d) (Fin d) F) : (p B)⁻¹=p (-B) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← actual_p_add,neg_add_cancel,p_zero]

theorem actual_p_upper (B : Matrix (Fin d) (Fin d) F) : LayerDepth 1 ((p B).val-1) := by
  intro i j hij
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
  simp only [Matrix.sub_apply,actual_p_entry,Matrix.one_apply,(evenLabel d).injective.eq_iff]
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [Matrix.one_apply]
    | inr j =>
      change (right j).val<(left i).val+1 at hij
      rw [left_val,right_val] at hij
      have hi := i.isLt; have hj := j.isLt
      omega
  | inr i => cases j <;> simp [Matrix.one_apply]

/-- The true P coordinate constraint, not an independently supplied
unitary parameterization. -/
def Skew (ι : RingAut F) (B : Matrix (Fin d) (Fin d) F) : Prop :=
  ∀ i j, ι (B j i)= -B i j

theorem actual_p_unitary_iff (ι : RingAut F) (B : Matrix (Fin d) (Fin d) F) :
    steinberg ι (p B)=p B ↔ Skew ι B := by
  constructor
  · intro hh i j
    have he := congrArg (fun g : SpecialLinearGroup (Fin (2*d)) F => g (left i) (right j)) hh
    rw [steinberg_entry,actual_p_inverse,rev_right,rev_left] at he
    change ι (p (-B) (evenLabel d (.inl j)) (evenLabel d (.inr i)))=_ at he
    simp only [left,right,actual_p_entry,fromBlocks_apply₁₂,Matrix.neg_apply,map_neg] at he
    exact neg_eq_iff_eq_neg.mp he
  · intro hB
    apply SpecialLinearGroup.ext
    intro i j
    obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
    obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
    rw [steinberg_entry,actual_p_inverse,← evenLabel_reflection,← evenLabel_reflection,
      actual_p_entry,actual_p_entry]
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [pairSwap,Matrix.one_apply,eq_comm]
      | inr j => simp [pairSwap,hB i j]
    | inr i =>
      cases j with
      | inl j => simp [pairSwap]
      | inr j => simp [pairSwap,Matrix.one_apply,eq_comm]

private theorem below_half_zero (b : SpecialLinearGroup (Fin (2*d)) F)
    (hb : LayerDepth 1 (b.val-1)) (i j : Fin d) : b (right i) (left j)=0 := by
  have hh := hb (right i) (left j) (by
    rw [right_val,left_val]; have hi := i.isLt; have hj := j.isLt; omega)
  simpa only [Matrix.sub_apply,Matrix.one_apply,right_ne_left,ite_false,sub_zero] using hh
private theorem upper_left_mul (a b : SpecialLinearGroup (Fin (2*d)) F)
    (hb : LayerDepth 1 (b.val-1)) (i j : Fin d) :
    (a*b) (left i) (left j)=∑ t : Fin d, a (left i) (left t)*b (left t) (left j) := by
  rw [SpecialLinearGroup.coe_mul,Matrix.mul_apply,← (evenLabel d).sum_comp,
    Fintype.sum_sum_type]
  change (∑ t : Fin d, a (left i) (left t)*b (left t) (left j))+
    (∑ t : Fin d, a (left i) (right t)*b (right t) (left j))=_
  simp only [below_half_zero b hb,mul_zero,Finset.sum_const_zero,add_zero]

private def top (b : SpecialLinearGroup (Fin (2*d)) F)
    (hb : LayerDepth 1 (b.val-1)) : SpecialLinearGroup (Fin d) F :=
  ⟨b.val.submatrix left left,by
    classical
    have ht : IsUpperTriangular (b.val.submatrix left left) := by
      intro i j hij
      have hijv : j.val < i.val := hij
      have hne : i≠j := ne_of_gt hij
      have hh := hb (left i) (left j) (by rw [left_val,left_val]; omega)
      simpa only [Matrix.sub_apply,Matrix.one_apply,left_inj.eq_iff,
        if_neg hne,sub_zero,Matrix.submatrix_apply] using hh
    rw [det_of_isUpperTriangular ht]
    apply Finset.prod_eq_one
    intro i hi
    have hh := hb (left i) (left i) (by omega)
    simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true,sub_eq_zero,Matrix.submatrix_apply] using hh⟩
private theorem top_upper (b : SpecialLinearGroup (Fin (2*d)) F)
    (hb : LayerDepth 1 (b.val-1)) : LayerDepth 1 ((top b hb).val-1) := by
  intro i j hij
  simpa only [top,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.one_apply,left_inj.eq_iff]
    using hb (left i) (left j) (by simpa only [left_val] using hij)
private theorem residual_top (b : SpecialLinearGroup (Fin (2*d)) F)
    (hb : LayerDepth 1 (b.val-1)) (ι : RingAut F) (i j : Fin d) :
    ((embed ι (top b hb))⁻¹*b) (left i) (left j)=(1:Matrix (Fin d) (Fin d) F) i j := by
  rw [← map_inv,upper_left_mul _ _ hb]
  have he := congrArg (fun g : SpecialLinearGroup (Fin d) F => g i j) (inv_mul_cancel (top b hb))
  simpa only [left,actual_typeA_levi_entry,fromBlocks_apply₁₁,top,Matrix.submatrix_apply,
    SpecialLinearGroup.coe_mul,Matrix.mul_apply,SpecialLinearGroup.coe_one] using he

/-- Actual even-dimensional p255 U=U2 P. The type-A block, P matrix,
and skew-Hermitian law are constructed from the actual target. -/
theorem actual_even_unitary_U_decomposition (ι : RingAut F) (hinv : Function.Involutive ι)
    (b : SpecialLinearGroup (Fin (2*d)) F) (hb : LayerDepth 1 (b.val-1))
    (hbu : steinberg ι b=b) :
    ∃ g : SpecialLinearGroup (Fin d) F, ∃ B : Matrix (Fin d) (Fin d) F,
      LayerDepth 1 (g.val-1) ∧ Skew ι B ∧ embed ι g*p B=b := by
  let g := top b hb
  let r := (embed ι g)⁻¹*b
  have hg := top_upper b hb
  have hr : LayerDepth 1 (r.val-1) := (unitRec% product_depth) 1 (by omega) _ _
    ((unitLayer% inverse_unit_depth) _ (actual_typeA_levi_upper ι hinv g hg).1) hb
  have hru : steinberg ι r=r := by
    dsimp only [r]; rw [map_mul,map_inv,actual_typeA_levi_unitary ι hinv,hbu]
  have htop : ∀ i j : Fin d, r (left i) (left j)=(1:Matrix (Fin d) (Fin d) F) i j :=
    residual_top b hb ι
  have hri := (unitLayer% inverse_unit_depth) r hr
  have hitop : ∀ i j : Fin d, r⁻¹ (left i) (left j)=(1:Matrix (Fin d) (Fin d) F) i j := by
    intro i j
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d)) F => a (left i) (left j)) (mul_inv_cancel r)
    rw [upper_left_mul _ _ hri] at hh
    simpa only [htop,Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true,SpecialLinearGroup.coe_one,left_inj.eq_iff] using hh
  have hbot : ∀ i j : Fin d, r (right i) (right j)=(1:Matrix (Fin d) (Fin d) F) i j := by
    intro i j
    have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d)) F => a (right i) (right j)) hru
    rw [steinberg_entry,rev_right,rev_right,hitop] at hh
    simpa only [Matrix.one_apply,eq_comm,apply_ite,map_one,map_zero] using hh.symm
  let B : Matrix (Fin d) (Fin d) F := fun i j => r (left i) (right j)
  have hrP : r=p B := by
    apply SpecialLinearGroup.ext
    intro i j
    obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
    obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
    rw [actual_p_entry]
    cases i with
    | inl i => cases j with
      | inl j => exact htop i j
      | inr j => rfl
    | inr i => cases j with
      | inl j => exact below_half_zero r hr i j
      | inr j => exact hbot i j
  refine ⟨g,B,hg,(actual_p_unitary_iff ι B).mp ?_,?_⟩
  · rw [← hrP]; exact hru
  · rw [← hrP]; dsimp only [r]; group
end NikolovSegal.PartIIUnitaryEvenP
