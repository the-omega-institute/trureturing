/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRelativeFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRelativeFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTypeALeviProduct
set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! Actual scalar arithmetic for PartII Proposition6.10 pp271–272.
Two consecutive batches replace the more economical Lemma7.1(b): the
first solves the relative-trace quotient, the second its trace-zero
kernel. Both consume the proved Lemma7.1(a) over the TRUE fixed field.
No scalar-surjectivity premise, characteristic restriction or full-F
correction is introduced. -/
namespace NikolovSegal.PartIIUnitaryRelativeFieldProduct
open UnitaryField PartIIFieldMaps
universe u
variable {F : Type u} [Field F] [Finite F]
private theorem commute (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (x : F) : ι (phi x)=phi (ι x) := by
  rw [involution_eq_pow ι hinv hne,involution_eq_pow ι hinv hne,map_pow]

private def restrict (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) : RingAut (fixedField ι) where
  toFun x := ⟨phi x.val,by rw [mem_fixedField,commute ι phi hinv hne]; exact congrArg phi ((mem_fixedField ι x.val).mp x.prop)⟩
  invFun x := ⟨phi.symm x.val,by rw [mem_fixedField,commute ι phi.symm hinv hne]; exact congrArg phi.symm ((mem_fixedField ι x.val).mp x.prop)⟩
  left_inv x := Subtype.ext (phi.symm_apply_apply x.val)
  right_inv x := Subtype.ext (phi.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul phi x.val y.val)
  map_add' x y := Subtype.ext (map_add phi x.val y.val)
private theorem restrict_pow (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (s : ℕ) (x : fixedField ι) :
    (((restrict ι phi hinv hne)^s) x:F)=(phi^s) (x:F) := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [pow_succ',RingAut.mul_apply]; exact congrArg phi ih
private theorem orbit_coe (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (s : ℕ) (a : fixedField ι) :
    ((orbitProduct (restrict ι phi hinv hne) s a : fixedField ι):F)=orbitProduct phi s (a:F) := by
  simp only [orbitProduct,SubmonoidClass.coe_finsetProd,restrict_pow]

private def tr (ι : RingAut F) (hinv : Function.Involutive ι) (x : F) : fixedField ι :=
  ⟨x+ι x,by rw [mem_fixedField,map_add,hinv x]; ring⟩
private theorem tr_sub (ι : RingAut F) (hinv : Function.Involutive ι) (x y : F) :
    tr ι hinv (x-y)=tr ι hinv x-tr ι hinv y := by
  apply Subtype.ext; simp only [tr,map_sub,Subfield.coe_sub]; ring
private theorem tr_sum {J : Type*} [Fintype J] (ι : RingAut F)
    (hinv : Function.Involutive ι) (x : J → F) :
    tr ι hinv (∑ j, x j)=∑ j, tr ι hinv (x j) := by
  apply Subtype.ext
  simp only [tr,AddSubmonoidClass.coe_finsetSum,map_sum,Finset.sum_add_distrib]
private theorem trace_value (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (s : ℕ) (a : fixedField ι) (t : F) :
    tr ι hinv (fieldValue phi 1 s 2 (a:F) t)=
      fieldValue (restrict ι phi hinv hne) 1 s 2 a (tr ι hinv t) := by
  apply Subtype.ext
  simp only [tr,fieldValue,one_mul,Subfield.coe_sub,Subfield.coe_mul,SubmonoidClass.coe_pow,
    orbit_coe,restrict_pow,map_sub,map_mul,map_pow]
  have hf : ι (orbitProduct phi s (a:F))=orbitProduct phi s (a:F) := by
    rw [← orbit_coe ι phi hinv hne]; exact (mem_fixedField ι _).mp (orbitProduct (restrict ι phi hinv hne) s a).prop
  rw [hf,commute ι (phi^s) hinv hne,map_add]
  ring

private theorem tracezero_exists (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) : ∃ tau : F, tau≠0 ∧ ι tau= -tau := by
  have hex : ∃ x : F, ι x≠x := by
    by_contra he; push_neg at he
    exact hne (RingEquiv.ext he)
  obtain ⟨x,hx⟩ := hex
  refine ⟨x-ι x,sub_ne_zero.mpr hx.symm,?_⟩
  rw [map_sub,hinv x]; ring
private def ratio (ι : RingAut F) (tau : F) (htau : tau≠0) (htrace : ι tau= -tau)
    (phi : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (s : ℕ) : fixedField ι :=
  ⟨(phi^s) tau/tau,by
    rw [mem_fixedField,map_div₀,commute ι (phi^s) hinv hne,htrace,map_neg]
    simp only [neg_div_neg_eq]⟩
private theorem ratio_ne (ι : RingAut F) (tau : F) (htau : tau≠0) (htrace : ι tau= -tau)
    (phi : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (s : ℕ) : ratio ι tau htau htrace phi hinv hne s≠0 := by
  intro hh
  have he := congrArg Subtype.val hh
  exact div_ne_zero ((map_ne_zero (phi^s)).mpr htau) htau he
private def zeroCoordinate (ι : RingAut F) (tau : F) (htau : tau≠0)
    (htrace : ι tau= -tau) (t : F) (ht : t+ι t=0) : fixedField ι :=
  ⟨t/tau,by
    rw [mem_fixedField,map_div₀,htrace,show ι t= -t by linear_combination ht]
    simp only [neg_div_neg_eq]⟩
private theorem scaled_value (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (tau : F) (htau : tau≠0) (htrace : ι tau= -tau)
    (s : ℕ) (a t : fixedField ι) :
    fieldValue phi 1 s 2 (a:F) (tau*(t:F))=
      tau*((fieldValue (restrict ι phi hinv hne)
        (ratio ι tau htau htrace phi hinv hne s) s 2 a t : fixedField ι):F) := by
  simp only [fieldValue,one_mul,map_mul,Subfield.coe_sub,Subfield.coe_mul,SubmonoidClass.coe_pow,
    orbit_coe,restrict_pow,ratio]
  field_simp

/-- Genuine relative-field PRODUCT arithmetic. Lambda belongs to F0;
BOTH batches and all coefficients are fixed before EVERY full-F target.
A trace-zero target also has witnesses ALL in the actual trace-zero
line. This is consumed by the skew-Hermitian P reconstruction. -/
theorem actual_relative_field_two_batch {q M : ℕ} (hq : 0<q)
    (hM : q*(2*q+1)<M) (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi0 phi1 : Fin M → RingAut F) (s0 s1 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q) :
    ∃ a0 a1 : Fin M → fixedField ι,
      (∀ j, a0 j≠0 ∧ a1 j≠0) ∧
      (∀ target : F, ∃ t0 t1 : Fin M → F,
        (∑ j, fieldValue (phi0 j) 1 (s0 j) 2 (a0 j:F) (t0 j))+
        (∑ j, fieldValue (phi1 j) 1 (s1 j) 2 (a1 j:F) (t1 j))=target) ∧
      (∀ target : F, target+ι target=0 → ∃ t1 : Fin M → F,
        (∀ j, t1 j+ι (t1 j)=0) ∧
        (∑ j, fieldValue (phi1 j) 1 (s1 j) 2 (a1 j:F) (t1 j))=target) := by
  classical
  letI : Fintype (fixedField ι) := Fintype.ofFinite _
  obtain ⟨tau,htau,htrace⟩ := tracezero_exists ι hinv hne
  obtain ⟨a0,ha0,h0⟩ := lemma7_1 (c:=2) hq hM (by simpa only [Nat.card_eq_fintype_card] using hK)
    (fun j => restrict ι (phi0 j) hinv hne) (fun _ => 1) s0 (fun _ => 2)
    (fun _ => one_ne_zero) hs0 (fun _ => ⟨by decide,by decide⟩)
  obtain ⟨a1,ha1,h1⟩ := lemma7_1 (c:=2) hq hM (by simpa only [Nat.card_eq_fintype_card] using hK)
    (fun j => restrict ι (phi1 j) hinv hne)
    (fun j => ratio ι tau htau htrace (phi1 j) hinv hne (s1 j)) s1 (fun _ => 2)
    (fun j => ratio_ne ι tau htau htrace (phi1 j) hinv hne (s1 j)) hs1
    (fun _ => ⟨by decide,by decide⟩)
  have hz : ∀ target : F, target+ι target=0 → ∃ t1 : Fin M → F,
      (∀ j, t1 j+ι (t1 j)=0) ∧
      (∑ j, fieldValue (phi1 j) 1 (s1 j) 2 (a1 j:F) (t1 j))=target := by
    intro target ht
    let v := zeroCoordinate ι tau htau htrace target ht
    obtain ⟨t,he⟩ := h1 v
    refine ⟨fun j => tau*(t j:F),?_,?_⟩
    · intro j
      rw [map_mul,htrace,(mem_fixedField ι (t j:F)).mp (t j).prop]; ring
    · simp only [scaled_value ι _ hinv hne tau htau htrace]
      rw [← Finset.mul_sum,← AddSubmonoidClass.coe_finsetSum]
      have heF := congrArg (fun z : fixedField ι => (z:F)) he
      dsimp only at heF
      rw [heF]
      change tau*(target/tau)=target
      exact mul_div_cancel₀ _ htau
  refine ⟨a0,a1,fun j => ⟨ha0 j,ha1 j⟩,?_,hz⟩
  intro target
  obtain ⟨v,hv⟩ := h0 (tr ι hinv target)
  have hl : ∀ j, ∃ t : F, tr ι hinv t=v j := by
    intro j
    obtain ⟨t,ht⟩ := trace_surjective ι hinv hne (v j)
    exact ⟨t,Subtype.ext ht⟩
  choose t0 ht0 using hl
  let P := ∑ j, fieldValue (phi0 j) 1 (s0 j) 2 (a0 j:F) (t0 j)
  have htP : tr ι hinv P=tr ι hinv target := by
    dsimp only [P]
    rw [tr_sum]
    simp only [trace_value ι _ hinv hne,ht0]
    exact hv
  have hr : (target-P)+ι (target-P)=0 := by
    have hh := congrArg Subtype.val (tr_sub ι hinv target P)
    rw [htP] at hh
    simpa only [tr,sub_self,Subfield.coe_zero] using hh
  obtain ⟨t1,_,he⟩ := hz (target-P) hr
  refine ⟨t0,t1,?_⟩
  change P+(∑ j, fieldValue (phi1 j) 1 (s1 j) 2 (a1 j:F) (t1 j))=target
  rw [he]; ring
end NikolovSegal.PartIIUnitaryRelativeFieldProduct
