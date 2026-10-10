/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalCornerFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalCornerFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalBoundaryFieldProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-! Actual central trace-zero V* corner PRODUCT, PartII pp262–263.
The accepted fixed-field scalar arithmetic is consumed with a true
SU torus and original positive divisor powers; all corner witnesses
are trace zero and no noncorner variable is introduced. -/
namespace NikolovSegal.PartIIUnitaryRadicalCornerFieldProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus PartIIFieldMaps UnitaryField
open PartIIUnitaryRadicalTraceCoordinates PartIIUnitaryRelativeFieldProduct
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}
private def corner (z : F) : SpecialLinearGroup (Fin (k+4)) F :=
  radical (fun _ => 0) (fun _ => 0) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ z
private theorem corner_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (z : F) (hz : z+ι z=0) : steinberg ι (corner (k:=k) z)=corner z := by
  exact actual_radical_unitary_of_trace ι hinv _ _ _ _ (by simp) _ (by simpa using hz)
private theorem corner_mul (z t : F) : corner (k:=k) z*corner t=corner (z+t) := by
  rw [corner,corner,actual_radical_mul]
  simp only [add_zero,zero_mul,Finset.sum_const_zero]
  rfl
private theorem corner_inv (z : F) : (corner (k:=k) z)⁻¹=corner (-z) := by
  rw [corner,actual_radical_inverse]
  simp only [neg_zero,zero_mul,Finset.sum_const_zero,add_zero]
  rfl
private theorem corner_zero : corner (F:=F) (k:=k) 0=1 := by
  apply SpecialLinearGroup.ext
  intro i j
  change (1:Matrix (Fin (k+4)) (Fin (k+4)) F) i j +
    (if i=first then (if j=last then 0 else 0) else if j=last then 0 else 0)=_
  simp
private theorem corner_ordered (z : Fin M → F) :
    orderedProduct (fun j => corner (k:=k) (z j))=corner (∑ j, z j) := by
  induction M with
  | zero => simp [orderedProduct,List.ofFn_zero,corner_zero]
  | succ M ih =>
    rw [orderedProduct,List.ofFn_succ,List.prod_cons,
      show (List.ofFn (fun j : Fin M => corner (k:=k) (z j.succ))).prod=
        corner (∑ j : Fin M, z j.succ) from ih (fun j => z j.succ),corner_mul,Fin.sum_univ_succ]
private theorem corner_entry (z : F) (i j : Fin (k+4)) :
    corner z i j=(1:Matrix (Fin (k+4)) (Fin (k+4)) F) i j+
      if i=first ∧ j=last then z else 0 := by
  change (1:Matrix (Fin (k+4)) (Fin (k+4)) F) i j+
    (if i=first then (if j=last then z else 0) else if j=last then 0 else 0)=_
  by_cases hi : i=first <;> by_cases hj : j=last <;> simp [hi,hj]
private theorem corner_diagonal_field (w : Fin (k+4) → Fˣ) (phi : RingAut F) (z : F) :
    PartIIProposition6_5.diagonalFieldGraph w phi false (corner z)=
      corner ((w first:F)*(w last:F)⁻¹*phi z) := by
  apply SpecialLinearGroup.ext
  intro i j
  change (unitOdd% diagonalAut) w (fieldAut phi (corner z)) i j=_
  rw [unitOdd% diagonal_entry]
  simp only [Units.val_inv_eq_inv_val]
  change (w i:F)*(phi ((corner z) i j))*(w j:F)⁻¹=_
  by_cases hij : i=j
  · subst j
    have he : ¬(i=first ∧ i=last) := by
      rintro ⟨rfl,he⟩
      have hh := congrArg Fin.val he
      simp only [first,last,Fin.val_zero,Fin.val_last] at hh
      omega
    simp [corner_entry,Matrix.one_apply,he]
  · by_cases he : i=first ∧ j=last
    · rcases he with ⟨rfl,rfl⟩
      have hne : (first:Fin (k+4))≠last := hij
      simp only [corner_entry,Matrix.one_apply,if_neg hne,zero_add,and_self,ite_true]
      ring
    · simp [corner_entry,Matrix.one_apply,hij,he]
private def weights (ι : RingAut F) (a : (fixedField ι)ˣ) : Fin (k+4) → Fˣ :=
  (vNormalize% innerWeights) ι (Units.map (fixedField ι).subtype a)
    ((Units.map (fixedField ι).subtype a)⁻¹)
private theorem weights_product (ι : RingAut F) (a : (fixedField ι)ˣ) :
    ∏ i, weights (k:=k) ι a i=1 := by
  rw [weights,vNormalize% innerWeights_product]
  simp [map_inv,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
private def action (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F) :
    MulAut (SpecialLinearGroup (Fin (k+4)) F) :=
  PartIIProposition6_5.diagonalFieldGraph (weights ι a) phi false
private theorem corner_step (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F) (z : F) :
    action ι a phi (corner (k:=k) z)=corner (((a:fixedField ι):F)^2*phi z) := by
  rw [action,corner_diagonal_field]
  have hl : weights (k:=k) ι a last=(involutionUnit ι (Units.map (fixedField ι).subtype a))⁻¹ := by
    change (Fin.cons (Units.map (fixedField ι).subtype a)
      (Fin.snoc ((unitaryCentral% extendWeights) ι (fun _ : Fin k => 1)
        ((Units.map (fixedField ι).subtype a)⁻¹))
        (involutionUnit ι (Units.map (fixedField ι).subtype a))⁻¹) : Fin (k+4) → Fˣ)
      (Fin.last (k+3))=_
    have he : (Fin.last (k+3):Fin (k+4))=(Fin.last (k+2)).succ := by apply Fin.ext; rfl
    rw [he,Fin.cons_succ,Fin.snoc_last]
  have h0 : weights (k:=k) ι a first=Units.map (fixedField ι).subtype a := rfl
  rw [hl,h0]
  congr 1
  simp only [Units.val_inv_eq_inv_val,inv_inv,involutionUnit_val]
  change ((a:fixedField ι):F)*ι ((a:fixedField ι):F)*phi z=_
  rw [(mem_fixedField ι _).mp (a:fixedField ι).prop]
  ring
private theorem corner_power (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F)
    (s : ℕ) (z : F) : (action ι a phi^s) (corner (k:=k) z)=
      corner ((orbitProduct phi s ((a:fixedField ι):F))^2*(phi^s) z) := by
  induction s with
  | zero => simp [orbitProduct]
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,ih,corner_step,rootFieldKernel% orbitProduct_succ,
      map_mul,map_pow,pow_succ' phi s,RingAut.mul_apply]
    congr 1
    ring
private theorem corner_value (ι : RingAut F) (a : (fixedField ι)ˣ) (phi : RingAut F)
    (s : ℕ) (z : F) : (corner (k:=k) z)⁻¹*(action ι a phi^s) (corner z)=
      corner (fieldValue phi 1 s 2 ((a:fixedField ι):F) z) := by
  rw [corner_inv,corner_power,corner_mul]
  congr 1
  simp only [fieldValue,one_mul]
  ring

/-- True trace-zero corner supplier. The SAME determinant-one unitary
h tuple is fixed before every trace-zero target and all witnesses are
actual central V* matrices. It CONSUMES the proved F0 scalar kernel,
not a supplied corner/whole-block coverage statement. -/
theorem actual_unitary_radical_corner_field_product {q : ℕ} (hq : 0<q)
    (hM : q*(2*q+1)<M) (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi : Fin M → RingAut F) (s : Fin M → ℕ) (hs : ∀ j, 0<s j ∧ s j∣q) :
    ∃ u : Fin M → (fixedField ι)ˣ, ∃ h : Fin M → SpecialLinearGroup (Fin (k+4)) F,
      (∀ j, h j=(radicalTorus% diagonalSL) (weights ι (u j)) (weights_product ι (u j))) ∧
      (∀ j, steinberg ι (h j)=h j) ∧
      ∀ target : F, target+ι target=0 →
        ∃ z : Fin M → F, ∃ x : Fin M → SpecialLinearGroup (Fin (k+4)) F,
          (∀ j, z j+ι (z j)=0) ∧
          (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
          (∀ j, x j=corner (z j)) ∧
          orderedProduct (fun j => (x j)⁻¹*
            ((MulAut.conj (h j)*fieldAut (n:=k+4) (phi j))^(s j)) (x j))=corner target := by
  classical
  obtain ⟨_,a,ha,_,hzero⟩ := actual_relative_field_two_batch hq hM ι hinv hne hK phi phi s s hs hs
  let u : Fin M → (fixedField ι)ˣ := fun j => Units.mk0 (a j) (ha j).2
  let h := fun j => (radicalTorus% diagonalSL) (weights (k:=k) ι (u j)) (weights_product ι (u j))
  have hhu : ∀ j, steinberg ι (h j)=h j := fun j =>
    (unitaryTorus% diagonal_fixed) ι _ _ ((vNormalize% innerWeights_unitary) ι hinv _ _)
  have he : ∀ j, MulAut.conj (h j)*fieldAut (n:=k+4) (phi j)=action ι (u j) (phi j) := by
    intro j
    dsimp only [h]
    rw [radicalTorus% diagonalSL_action]
    rfl
  refine ⟨u,h,fun _ => rfl,hhu,?_⟩
  intro target ht
  obtain ⟨z,hz,hprod⟩ := hzero target ht
  let x := fun j => corner (k:=k) (z j)
  refine ⟨z,x,hz,fun j => ⟨actual_radical_mem _ _ _ _ _,corner_unitary ι hinv _ (hz j)⟩,fun _ => rfl,?_⟩
  simp only [he]
  change orderedProduct (fun j => (corner (k:=k) (z j))⁻¹*(action ι (u j) (phi j)^(s j)) (corner (z j)))=_
  simp only [corner_value]
  rw [corner_ordered]
  have hh : (∑ j, fieldValue (phi j) 1 (s j) 2 (((u j: (fixedField ι)ˣ):fixedField ι):F) (z j))=target := by
    simpa only [u,Units.val_mk0] using hprod
  rw [hh]
end NikolovSegal.PartIIUnitaryRadicalCornerFieldProduct
