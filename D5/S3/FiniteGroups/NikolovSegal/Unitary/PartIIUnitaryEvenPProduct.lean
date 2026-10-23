/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryEvenP
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRelativeFieldProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
/-! Actual even-dimensional Proposition6.10. Real skew-Hermitian
coordinates consume the proved relative trace/kernel scalar arithmetic.
One ambient determinant-one unitary correction tuple is fixed before
all P targets. No P coverage, coordinate or scalar oracle is assumed. -/
namespace NikolovSegal.PartIIUnitaryEvenPProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIUnitaryUpperTorus PartIIUnitaryEvenP UnitaryField PartIIFieldMaps
open PartIIUnitaryRelativeFieldProduct
universe u
variable {F : Type u} [Field F] [Finite F] {d M : ℕ}

private theorem reflect_value (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (s : ℕ) (a : fixedField ι) (t : F) :
    fieldValue phi 1 s 2 (a:F) (-ι t)= -ι (fieldValue phi 1 s 2 (a:F) t) := by
  have hc : ∀ x : F, ι (phi x)=phi (ι x) := by
    intro x
    rw [involution_eq_pow ι hinv hne,involution_eq_pow ι hinv hne,map_pow]
  have hcp : ∀ n x, ι ((phi^n) x)=(phi^n) (ι x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ',RingAut.mul_apply,hc,ih]
  have hf : ι (orbitProduct phi s (a:F))=orbitProduct phi s (a:F) := by
    simp only [orbitProduct,map_prod,hcp,(mem_fixedField ι (a:F)).mp a.prop]
  simp only [fieldValue,one_mul,map_sub,map_mul,map_pow,map_neg,hcp,hf]
  ring
private def symmetrize (ι : RingAut F) (t : Fin d → Fin d → F) : Matrix (Fin d) (Fin d) F :=
  fun i j => if i≤j then t i j else -ι (t j i)
private theorem symmetrize_skew (ι : RingAut F) (hinv : Function.Involutive ι)
    (t : Fin d → Fin d → F) (ht : ∀ i, t i i+ι (t i i)=0) : Skew ι (symmetrize ι t) := by
  intro i j
  rcases lt_trichotomy i j with hij|he|hji
  · simp only [symmetrize,if_pos (le_of_lt hij),if_neg (not_le_of_gt hij),map_neg,hinv (t i j)]
  · subst j
    simp only [symmetrize,if_pos (le_refl i)]
    linear_combination ht i
  · simp only [symmetrize,if_pos (le_of_lt hji),if_neg (not_le_of_gt hji),neg_neg]

private theorem p_ordered_sum (B : Fin M → Matrix (Fin d) (Fin d) F) :
    NikolovSegal.orderedProduct (fun j => p (B j))=p (∑ j, B j) := by
  induction M with
  | zero =>
    simp only [NikolovSegal.orderedProduct,List.ofFn_zero,List.prod_nil,Finset.univ_eq_empty,Finset.sum_empty]
    have h : p (0:Matrix (Fin d) (Fin d) F)=p 0*p 0 := by
      simpa only [zero_add] using actual_p_add (0:Matrix (Fin d) (Fin d) F) 0
    have hh := congrArg (fun z : SpecialLinearGroup (Fin (2*d)) F => (p (0:Matrix (Fin d) (Fin d) F))⁻¹*z) h
    simpa only [← mul_assoc,inv_mul_cancel,one_mul] using hh
  | succ M ih =>
    simp only [NikolovSegal.orderedProduct,List.ofFn_succ,List.prod_cons]
    change p (B 0)*NikolovSegal.orderedProduct (fun j => p (B j.succ))=_
    rw [ih,← actual_p_add,Fin.sum_univ_succ]

/-- Simultaneous reconstruction of ALL genuine P coordinates. Upper
parameters are freely solved, their paired entries are forced by the
true involution, and diagonal witnesses lie in the trace-zero line. -/
theorem actual_skew_two_batch {q : ℕ} (hq : 0<q) (hM : q*(2*q+1)<M)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi0 phi1 : Fin M → RingAut F) (s0 s1 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q) :
    ∃ a0 a1 : Fin M → fixedField ι,
      (∀ j, a0 j≠0 ∧ a1 j≠0) ∧
      ∀ B : Matrix (Fin d) (Fin d) F, Skew ι B →
        ∃ T0 T1 : Fin M → Matrix (Fin d) (Fin d) F,
          (∀ j, Skew ι (T0 j) ∧ Skew ι (T1 j)) ∧
          (∑ j, fun r c => fieldValue (phi0 j) 1 (s0 j) 2 (a0 j:F) (T0 j r c))+
          (∑ j, fun r c => fieldValue (phi1 j) 1 (s1 j) 2 (a1 j:F) (T1 j r c))=B := by
  classical
  obtain ⟨a0,a1,ha,hfull,hzero⟩ := actual_relative_field_two_batch hq hM ι hinv hne hK phi0 phi1 s0 s1 hs0 hs1
  refine ⟨a0,a1,ha,?_⟩
  intro B hB
  have ht : ∀ r c : Fin d, ∃ t0 t1 : Fin M → F,
      (∑ j, fieldValue (phi0 j) 1 (s0 j) 2 (a0 j:F) (t0 j))+
      (∑ j, fieldValue (phi1 j) 1 (s1 j) 2 (a1 j:F) (t1 j))=B r c ∧
      (r=c → ∀ j, t0 j+ι (t0 j)=0 ∧ t1 j+ι (t1 j)=0) := by
    intro r c
    by_cases he : r=c
    · subst c
      obtain ⟨t,ht,hv⟩ := hzero (B r r) (by linear_combination hB r r)
      refine ⟨fun _ => 0,t,?_,fun _ j => ⟨by simp,ht j⟩⟩
      simpa [fieldValue] using hv
    · obtain ⟨t0,t1,hv⟩ := hfull (B r c)
      exact ⟨t0,t1,hv,fun hh => (he hh).elim⟩
  choose t0 t1 hv ht using ht
  let T0 := fun j => symmetrize ι (fun r c => t0 r c j)
  let T1 := fun j => symmetrize ι (fun r c => t1 r c j)
  refine ⟨T0,T1,fun j => ⟨symmetrize_skew ι hinv _ (fun i => (ht i i rfl j).1),
    symmetrize_skew ι hinv _ (fun i => (ht i i rfl j).2)⟩,?_⟩
  ext r c
  simp only [Pi.add_apply,Finset.sum_apply]
  by_cases hrc : r≤c
  · simpa only [T0,T1,symmetrize,if_pos hrc] using hv r c
  · have hcr : c≤r := le_of_lt (lt_of_not_ge hrc)
    simp only [T0,T1,symmetrize,if_neg hrc,reflect_value ι _ hinv hne]
    rw [Finset.sum_neg_distrib,Finset.sum_neg_distrib,← map_sum,← map_sum,
      ← neg_add,← map_add,hv c r,hB r c,neg_neg]

private def weights (ι : RingAut F) (a : (fixedField ι)ˣ) : Fin (2*d) → Fˣ :=
  fun i => Sum.elim (fun _ => Units.map (Subfield.subtype (fixedField ι)).toMonoidHom a)
    (fun _ => (Units.map (Subfield.subtype (fixedField ι)).toMonoidHom a)⁻¹) ((evenLabel d).symm i)
private theorem weights_unitary (ι : RingAut F) (a : (fixedField ι)ˣ) (i : Fin (2*d)) :
    ι (weights (d:=d) ι a i:F)*(weights ι a i.rev:F)=1 := by
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  rw [← evenLabel_reflection]
  have hf : ι ((a:fixedField ι):F)=((a:fixedField ι):F) := (mem_fixedField ι _).mp a.val.prop
  cases i <;> simp [weights,pairSwap,Units.val_inv_eq_inv_val,map_inv₀,hf]
private def action (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F) :
    MulAut (SpecialLinearGroup (Fin (2*d)) F) := (unitOdd% diagonalAut) (weights ι a)*fieldAut phi
private theorem action_p (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F)
    (B : Matrix (Fin d) (Fin d) F) :
    action ι a phi (p B)=p (fun i j => (((a:fixedField ι):F)^2)*phi (B i j)) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
  change ((unitOdd% diagonalAut) (weights ι a) (fieldAut phi (p B))) (evenLabel d i) (evenLabel d j)=_
  rw [unitOdd% diagonal_entry]
  change (weights ι a (evenLabel d i):F)*phi (p B (evenLabel d i) (evenLabel d j))*
    (((weights ι a (evenLabel d j))⁻¹:Fˣ):F)=_
  rw [actual_p_entry,actual_p_entry]
  cases i with
  | inl i => cases j with
    | inl j => by_cases hij : i=j <;> simp [weights,Matrix.one_apply,hij]
    | inr j => simp [weights,pow_two,mul_assoc,mul_comm,mul_left_comm]
  | inr i => cases j with
    | inl j => simp [weights]
    | inr j => by_cases hij : i=j <;> simp [weights,Matrix.one_apply,hij]
private theorem action_power_p (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F)
    (s : ℕ) (B : Matrix (Fin d) (Fin d) F) :
    (action ι a phi^s) (p B)=p (fun i j => (orbitProduct phi s ((a:fixedField ι):F))^2*(phi^s) (B i j)) := by
  induction s generalizing B with
  | zero => simp [orbitProduct]
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,ih,action_p]
    congr 1; funext i j
    rw [rootFieldKernel% orbitProduct_succ]
    simp only [map_mul,map_pow,pow_succ',RingAut.mul_apply]
    ring
private theorem value_p (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F)
    (s : ℕ) (B : Matrix (Fin d) (Fin d) F) :
    (p B)⁻¹*(action ι a phi^s) (p B)=
      p (fun i j => fieldValue phi 1 s 2 ((a:fixedField ι):F) (B i j)) := by
  rw [actual_p_inverse,action_power_p,← actual_p_add]
  congr 1; funext i j
  simp only [fieldValue,one_mul,Matrix.add_apply,Matrix.neg_apply]; ring

/-- Actual even P VALUE PRODUCT inside the ambient SU(2d+2).
Both genuine INNER UNITARY correction batches precede ALL targets;
all original positive divisor powers and ordered VALUES are retained. -/
theorem actual_even_P_two_batch_inner_product {q : ℕ} (hq : 0<q) (hM : q*(2*q+1)<M)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi0 phi1 : Fin M → RingAut F) (s0 s1 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q) :
    ∃ h0 h1 : Fin M → SpecialLinearGroup (Fin (2*d+2)) F,
      (∀ j, steinberg ι (h0 j)=h0 j ∧ steinberg ι (h1 j)=h1 j) ∧
      (∀ j, ∀ g : SpecialLinearGroup (Fin (2*d)) F,
        (∃ z : SpecialLinearGroup (Fin (2*d)) F, (MulAut.conj (h0 j)) (PartIICentralLevi.embed g)=PartIICentralLevi.embed z) ∧
        (∃ z : SpecialLinearGroup (Fin (2*d)) F, (MulAut.conj (h1 j)) (PartIICentralLevi.embed g)=PartIICentralLevi.embed z)) ∧
      ∀ B : Matrix (Fin d) (Fin d) F, Skew ι B →
        ∃ T0 T1 : Fin M → Matrix (Fin d) (Fin d) F,
          (∀ j, Skew ι (T0 j) ∧ Skew ι (T1 j)) ∧
          NikolovSegal.orderedProduct (fun j => (PartIICentralLevi.embed (p (T0 j)))⁻¹*
            ((MulAut.conj (h0 j)*fieldAut (n:=2*d+2) (phi0 j))^(s0 j)) (PartIICentralLevi.embed (p (T0 j))))*
          NikolovSegal.orderedProduct (fun j => (PartIICentralLevi.embed (p (T1 j)))⁻¹*
            ((MulAut.conj (h1 j)*fieldAut (n:=2*d+2) (phi1 j))^(s1 j)) (PartIICentralLevi.embed (p (T1 j))))=
          PartIICentralLevi.embed (p B) := by
  classical
  obtain ⟨a0,a1,ha,hcover⟩ := actual_skew_two_batch (d:=d) hq hM ι hinv hne hK phi0 phi1 s0 s1 hs0 hs1
  let u0 : Fin M → (fixedField ι)ˣ := fun j => Units.mk0 (a0 j) (ha j).1
  let u1 : Fin M → (fixedField ι)ˣ := fun j => Units.mk0 (a1 j) (ha j).2
  have hc : ∀ a : (fixedField ι)ˣ, ∃ h : SpecialLinearGroup (Fin (2*d+2)) F,
      steinberg ι h=h ∧ ∀ g : SpecialLinearGroup (Fin (2*d)) F,
        (MulAut.conj h) (PartIICentralLevi.embed g)=PartIICentralLevi.embed ((unitOdd% diagonalAut) (weights ι a) g) := by
    intro a
    obtain ⟨h,_,hhu,hh⟩ := PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
      ι hinv hne (weights ι a) 1 (weights_unitary ι a)
    exact ⟨h,hhu,hh⟩
  choose h hh hact using hc
  have hp : ∀ a : (fixedField ι)ˣ, ∀ phi : RingAut F, ∀ s : ℕ, ∀ g : SpecialLinearGroup (Fin (2*d)) F,
      ((MulAut.conj (h a)*fieldAut (n:=2*d+2) phi)^s) (PartIICentralLevi.embed g)=
        PartIICentralLevi.embed ((action ι a phi^s) g) := by
    intro a phi s
    induction s with
    | zero => intro g; rfl
    | succ s ih =>
      intro g
      rw [pow_succ',MulAut.mul_apply,ih,MulAut.mul_apply,centralKernel% field_embed,hact,
        pow_succ',MulAut.mul_apply]
      rfl
  refine ⟨fun j => h (u0 j),fun j => h (u1 j),fun j => ⟨hh _,hh _⟩,
    fun j g => ⟨⟨_,hact (u0 j) g⟩,⟨_,hact (u1 j) g⟩⟩,?_⟩
  intro B hB
  obtain ⟨T0,T1,hT,he⟩ := hcover B hB
  refine ⟨T0,T1,hT,?_⟩
  simp only [hp,← map_inv,← map_mul,value_p]
  simp only [u0,u1,Units.val_mk0]
  have hm : ∀ v : Fin M → SpecialLinearGroup (Fin (2*d)) F,
      NikolovSegal.orderedProduct (fun j => PartIICentralLevi.embed (v j))=
        PartIICentralLevi.embed (NikolovSegal.orderedProduct v) := by
    intro v
    simp only [NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]
  rw [hm,hm,p_ordered_sum,p_ordered_sum,← map_mul,← actual_p_add,he]
end NikolovSegal.PartIIUnitaryEvenPProduct
