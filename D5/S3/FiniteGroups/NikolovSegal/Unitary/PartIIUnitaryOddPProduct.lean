/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryOddP
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Lean Elab Term in
elab "oddP%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryOddP"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) => n.toString.endsWith suffix && match env.getModuleIdxFor? n with
    | none => false
    | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryOddP"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual odd P coordinate kernel {id} not found"
namespace NikolovSegal.PartIIUnitaryOddPProduct
open Matrix PartIIUnitaryOddP PartIIUnitaryUpperTorus UnitaryField PartIIFieldMaps
open PartIIUnitriangularActions PartIIUnitriangularLayers PartIIUnitaryRelativeFieldProduct
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}

private def w (a : Fˣ) : Fin (2*d+1) → Fˣ :=
  fun i => Sum.elim (fun _ => a) (Sum.elim (fun _ => 1) (fun _ => a⁻¹)) ((oddP% label).symm i)
private theorem w_product (a : Fˣ) : ∏ i, w (d:=d) a i=1 := by
  rw [← (oddP% label).prod_comp (w (d:=d) a)]
  simp [w,Fintype.prod_sum_type]
private def torus (a : Fˣ) : SpecialLinearGroup (Fin (2*d+1)) F :=
  (radicalTorus% diagonalSL) (w a) (w_product a)
private theorem torus_diagonal (a : Fˣ) (i j : Fin (2*d+1)) (hij : i≠j) : torus a i j=0 := by
  change Matrix.diagonal (fun i => (w a i:F)) i j=0
  simp [Matrix.diagonal_apply,hij]
private theorem torus_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (a : Fˣ) (ha : ι (a:F)=(a:F)) : steinberg ι (torus (d:=d) a)=torus a := by
  apply (unitaryTorus% diagonal_fixed) ι (w a) (w_product a)
  intro i
  obtain ⟨i,rfl⟩ := (oddP% label).surjective i
  rw [← oddP% label_reflection]
  cases i with
  | inl i =>
    rw [show (oddP% swap) (.inl i)=.inr (.inr i) from rfl]
    simp [w,ha,Units.val_inv_eq_inv_val]
  | inr i => cases i with
    | inl i =>
      rw [show (oddP% swap) (.inr (.inl i))=.inr (.inl i) from rfl]
      simp [w]
    | inr i =>
      rw [show (oddP% swap) (.inr (.inr i))=.inl i from rfl]
      simp [w,ha,Units.val_inv_eq_inv_val]
private theorem commute (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (x : F) : phi (ι x)=ι (phi x) := by
  rw [involution_eq_pow ι hinv hne,map_pow,involution_eq_pow ι hinv hne]
private def action (a : Fˣ) (phi : RingAut F) : MulAut (SpecialLinearGroup (Fin (2*d+1)) F) :=
  MulAut.conj (torus a)*fieldAut phi
private theorem action_p (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fˣ) (ha : ι (a:F)=(a:F))
    (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    action a phi (p ι v B)=p ι (fun i => (a:F)*phi (v i))
      (fun i j => (a:F)^2*phi (B i j)) := by
  change (MulAut.conj (torus a)) (fieldAut phi (p ι v B))=_
  dsimp only [torus]
  rw [radicalTorus% diagonalSL_action]
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := (oddP% label).surjective i
  obtain ⟨j,rfl⟩ := (oddP% label).surjective j
  rw [unitOdd% diagonal_entry]
  rw [show (fieldAut phi (p ι v B)) ((oddP% label) i) ((oddP% label) j)=phi (p ι v B ((oddP% label) i) ((oddP% label) j)) from rfl]
  rw [Units.val_inv_eq_inv_val]
  rw [actual_p_entry,actual_p_entry]
  change (w a ((oddP% label) i):F)*
    phi ((fromBlocks 1 (fromCols (fun i _ => v i) B) 0 (fromBlocks 1 (fun _ j => -ι (v j)) 0 1)) i j)*
    ((w a ((oddP% label) j):F)⁻¹)=
    (fromBlocks 1 (fromCols (fun i _ => (a:F)*phi (v i)) (fun i j => (a:F)^2*phi (B i j))) 0
      (fromBlocks 1 (fun _ j => -ι ((a:F)*phi (v j))) 0 1)) i j
  cases i with
  | inl i => cases j with
    | inl j => simp [w,Matrix.one_apply,Units.val_inv_eq_inv_val] <;> split_ifs <;> simp
    | inr j => cases j <;> simp [w,Units.val_inv_eq_inv_val,pow_two] <;> ring
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp [w]
      | inr j => cases j <;> simp [w,Units.val_inv_eq_inv_val,map_mul,map_neg,ha,commute ι phi hinv hne] <;> ring
    | inr i => cases j with
      | inl j => simp [w]
      | inr j => cases j <;> simp [w,Matrix.one_apply,Units.val_inv_eq_inv_val] <;> split_ifs <;> simp
private theorem action_power_p (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fˣ) (ha : ι (a:F)=(a:F)) (s : ℕ)
    (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    (action a phi^s) (p ι v B)=p ι
      (fun i => orbitProduct phi s (a:F)*(phi^s) (v i))
      (fun i j => (orbitProduct phi s (a:F))^2*(phi^s) (B i j)) := by
  induction s with
  | zero => simp [orbitProduct]
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,ih,action_p ι phi hinv hne a ha,
      rootFieldKernel% orbitProduct_succ]
    congr 1
    · funext i; simp only [pow_succ',RingAut.mul_apply,map_mul]; ring
    · ext i j; simp only [pow_succ',RingAut.mul_apply,map_mul,map_pow]; ring

private theorem field_unitary (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : SpecialLinearGroup (Fin (2*d+1)) F)
    (hg : steinberg ι g=g) : steinberg ι (fieldAut phi g)=fieldAut phi g := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,← map_inv]
  change ι (phi (g⁻¹ j.rev i.rev))=phi (g i j)
  rw [← commute ι phi hinv hne]
  have he := congrArg (fun h : SpecialLinearGroup (Fin (2*d+1)) F => h i j) hg
  rw [steinberg_entry] at he
  exact congrArg phi he
private theorem action_unitary (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fˣ) (ha : ι (a:F)=(a:F))
    (g : SpecialLinearGroup (Fin (2*d+1)) F) (hg : steinberg ι g=g) :
    steinberg ι (action a phi g)=action a phi g := by
  simp only [action,MulAut.mul_apply,MulAut.conj_apply]
  rw [map_mul,map_mul,map_inv,torus_unitary ι hinv a ha,field_unitary ι phi hinv hne g hg]
private theorem power_unitary (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fˣ) (ha : ι (a:F)=(a:F)) (s : ℕ)
    (g : SpecialLinearGroup (Fin (2*d+1)) F) (hg : steinberg ι g=g) :
    steinberg ι ((action a phi^s) g)=(action a phi^s) g := by
  induction s with
  | zero => exact hg
  | succ s ih => rw [pow_succ',MulAut.mul_apply]; exact action_unitary ι phi hinv hne a ha _ ih
private theorem value_p (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fˣ) (ha : ι (a:F)=(a:F)) (s : ℕ)
    (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    ∃ C : Matrix (Fin d) (Fin d) F,
      (p ι v B)⁻¹*(action a phi^s) (p ι v B)=
        p ι (fun i => fieldValue phi 1 s 1 (a:F) (v i)) C := by
  rw [action_power_p ι phi hinv hne a ha,actual_p_inverse,actual_p_multiply]
  refine ⟨(-B-(Matrix.of fun i j => v i*ι (v j)))+
    (Matrix.of fun i j => (orbitProduct phi s (a:F))^2*(phi^s) (B i j))-
    (Matrix.of fun i j => (-v) i*ι (orbitProduct phi s (a:F)*(phi^s) (v j))),?_⟩
  congr 1
  funext i
  simp only [Pi.add_apply,Pi.neg_apply,fieldValue,one_mul,pow_one]
  ring
private theorem ordered_p {M : ℕ} (ι : RingAut F) (v : Fin M → Fin d → F)
    (B : Fin M → Matrix (Fin d) (Fin d) F) :
    ∃ C : Matrix (Fin d) (Fin d) F, orderedProduct (fun j => p ι (v j) (B j))=p ι (∑ j, v j) C := by
  induction M with
  | zero => refine ⟨0,?_⟩; simp only [orderedProduct,List.ofFn_zero,List.prod_nil,Finset.univ_eq_empty,Finset.sum_empty]; exact (oddP% p_zero) ι |>.symm
  | succ M ih =>
    obtain ⟨C,hC⟩ := ih (fun j => v j.succ) (fun j => B j.succ)
    refine ⟨B 0+C-(Matrix.of fun i j => v 0 i*ι ((∑ t : Fin M, v t.succ) j)),?_⟩
    rw [orderedProduct,List.ofFn_succ,List.prod_cons]
    change p ι (v 0) (B 0)*orderedProduct (fun j => p ι (v j.succ) (B j.succ))=_
    rw [hC,actual_p_multiply,Fin.sum_univ_succ]
private def values {M : ℕ} (a : Fin M → Fˣ) (phi : Fin M → RingAut F) (s : Fin M → ℕ)
    (x : Fin M → SpecialLinearGroup (Fin (2*d+1)) F) :=
    orderedProduct (fun j => (x j)⁻¹*(action (a j) (phi j)^s j) (x j))
private theorem values_unitary {M : ℕ} (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fin M → Fˣ) (ha : ∀ j, ι (a j:F)=(a j:F))
    (phi : Fin M → RingAut F) (s : Fin M → ℕ)
    (x : Fin M → SpecialLinearGroup (Fin (2*d+1)) F) (hx : ∀ j, steinberg ι (x j)=x j) :
    steinberg ι (values a phi s x)=values a phi s x := by
  have hv : ∀ j, steinberg ι ((x j)⁻¹*(action (a j) (phi j)^s j) (x j))=
      (x j)⁻¹*(action (a j) (phi j)^s j) (x j) := by
    intro j
    rw [map_mul,map_inv,hx j,power_unitary ι (phi j) hinv hne (a j) (ha j) (s j) (x j) (hx j)]
  simp only [values,orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def,hv]
private theorem values_vector {M : ℕ} (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fin M → Fˣ) (ha : ∀ j, ι (a j:F)=(a j:F))
    (phi : Fin M → RingAut F) (s : Fin M → ℕ)
    (v : Fin M → Fin d → F) (B : Fin M → Matrix (Fin d) (Fin d) F) :
    ∃ C : Matrix (Fin d) (Fin d) F, values a phi s (fun j => p ι (v j) (B j))=
      p ι (fun i => ∑ j, fieldValue (phi j) 1 (s j) 1 (a j:F) (v j i)) C := by
  have hc := fun j => value_p ι (phi j) hinv hne (a j) (ha j) (s j) (v j) (B j)
  choose C hC using hc
  obtain ⟨D,hD⟩ := ordered_p ι (fun j i => fieldValue (phi j) 1 (s j) 1 (a j:F) (v j i)) C
  refine ⟨D,?_⟩
  simp only [values,hC]
  have hv : (∑ j, fun i => fieldValue (phi j) 1 (s j) 1 (a j:F) (v j i))=
      (fun i => ∑ j, fieldValue (phi j) 1 (s j) 1 (a j:F) (v j i)) := by
    funext i; exact Finset.sum_apply i Finset.univ _
  rw [hv] at hD
  exact hD
private theorem squared_fieldValue (phi : RingAut F) (s : ℕ) (a t : F) :
    fieldValue phi 1 s 1 (a^2) t=fieldValue phi 1 s 2 a t := by
  simp only [fieldValue,orbitProduct,map_pow,Finset.prod_pow,one_mul,pow_one]
private def liftUnit (ι : RingAut F) (a : fixedField ι) (ha : a≠0) : Fˣ :=
  Units.mk0 (a:F) (by intro h; exact ha (Subtype.ext h))

/-- Genuine vector-quotient VALUE reconstruction in TWO ordered batches.
The fixed-field torus corrections precede all vector targets, witnesses
are actual positive-unitary P matrices, and the central cross terms are
retained as the actual unitary residual, rather than assumed covered. -/
theorem actual_odd_P_vector_two_batch {q M : ℕ} (hq : 0<q)
    (hM : q*(2*q+1)<M) (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi0 phi1 : Fin M → RingAut F) (s0 s1 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q) :
    ∃ a0 a1 : Fin M → Fˣ,
      (∀ j, ι (a0 j:F)=(a0 j:F) ∧ ι (a1 j:F)=(a1 j:F)) ∧
      (∀ j, steinberg ι (torus (d:=d) (a0 j))=torus (a0 j) ∧
        steinberg ι (torus (d:=d) (a1 j))=torus (a1 j)) ∧
      ∀ v : Fin d → F, ∃ x0 x1 : Fin M → SpecialLinearGroup (Fin (2*d+1)) F,
        ∃ C : Matrix (Fin d) (Fin d) F,
          (∀ j, LayerDepth 1 ((x0 j).val-1) ∧ steinberg ι (x0 j)=x0 j ∧
            LayerDepth 1 ((x1 j).val-1) ∧ steinberg ι (x1 j)=x1 j) ∧
          Constraint ι v C ∧ values a0 phi0 s0 x0*values a1 phi1 s1 x1=p ι v C := by
  classical
  obtain ⟨b0,b1,hb,hfull,_⟩ := actual_relative_field_two_batch hq hM ι hinv hne hK phi0 phi1 s0 s1 hs0 hs1
  let a0 := fun j => (liftUnit ι (b0 j) (hb j).1)^2
  let a1 := fun j => (liftUnit ι (b1 j) (hb j).2)^2
  have ha0 : ∀ j, ι (a0 j:F)=(a0 j:F) := by
    intro j; simpa only [a0,liftUnit,Units.val_pow_eq_pow_val,Units.val_mk0,map_pow] using
      congrArg (fun x : F => x^2) ((mem_fixedField ι (b0 j:F)).mp (b0 j).prop)
  have ha1 : ∀ j, ι (a1 j:F)=(a1 j:F) := by
    intro j; simpa only [a1,liftUnit,Units.val_pow_eq_pow_val,Units.val_mk0,map_pow] using
      congrArg (fun x : F => x^2) ((mem_fixedField ι (b1 j:F)).mp (b1 j).prop)
  refine ⟨a0,a1,fun j => ⟨ha0 j,ha1 j⟩,fun j =>
    ⟨torus_unitary ι hinv _ (ha0 j),torus_unitary ι hinv _ (ha1 j)⟩,?_⟩
  intro v
  have ht := fun i : Fin d => hfull (v i)
  choose t0 t1 ht using ht
  have hv0 := fun j : Fin M => actual_p_vector_lift ι hinv hne (fun i => t0 i j)
  have hv1 := fun j : Fin M => actual_p_vector_lift ι hinv hne (fun i => t1 i j)
  choose B0 hB0 hu0 hU0 using hv0
  choose B1 hB1 hu1 hU1 using hv1
  let x0 := fun j => p ι (fun i => t0 i j) (B0 j)
  let x1 := fun j => p ι (fun i => t1 i j) (B1 j)
  obtain ⟨C0,hC0⟩ := values_vector ι hinv hne a0 ha0 phi0 s0 (fun j i => t0 i j) B0
  obtain ⟨C1,hC1⟩ := values_vector ι hinv hne a1 ha1 phi1 s1 (fun j i => t1 i j) B1
  let v0 : Fin d → F := fun i => ∑ j, fieldValue (phi0 j) 1 (s0 j) 2 (b0 j:F) (t0 i j)
  let v1 : Fin d → F := fun i => ∑ j, fieldValue (phi1 j) 1 (s1 j) 2 (b1 j:F) (t1 i j)
  have he0 : values a0 phi0 s0 x0=p ι v0 C0 := by simpa only [a0,liftUnit,x0,v0,Units.val_pow_eq_pow_val,Units.val_mk0,squared_fieldValue] using hC0
  have he1 : values a1 phi1 s1 x1=p ι v1 C1 := by simpa only [a1,liftUnit,x1,v1,Units.val_pow_eq_pow_val,Units.val_mk0,squared_fieldValue] using hC1
  have hv : v0+v1=v := by funext i; exact ht i
  let C := C0+C1-(Matrix.of fun i j => v0 i*ι (v1 j))
  have he : values a0 phi0 s0 x0*values a1 phi1 s1 x1=p ι v C := by
    rw [he0,he1,actual_p_multiply,hv]
  have hu : steinberg ι (p ι v C)=p ι v C := by
    rw [← he,map_mul,values_unitary ι hinv hne a0 ha0 phi0 s0 x0 hu0,
      values_unitary ι hinv hne a1 ha1 phi1 s1 x1 hu1]
  exact ⟨x0,x1,C,fun j => ⟨hU0 j,hu0 j,hU1 j,hu1 j⟩,(actual_p_unitary_iff ι hinv v C).mp hu,he⟩

private theorem central_add (ι : RingAut F) (B C : Matrix (Fin d) (Fin d) F) :
    p ι 0 B*p ι 0 C=p ι 0 (B+C) := by
  have h := actual_p_multiply ι (0:Fin d → F) 0 B C
  have hz : (Matrix.of fun i j : Fin d => (0:F))=0 := by ext i j; rfl
  simpa only [add_zero,Pi.zero_apply,mul_zero,map_zero,hz,sub_zero] using h
private theorem ordered_central {M : ℕ} (ι : RingAut F) (B : Fin M → Matrix (Fin d) (Fin d) F) :
    orderedProduct (fun j => p ι 0 (B j))=p ι 0 (∑ j, B j) := by
  induction M with
  | zero => simp only [orderedProduct,List.ofFn_zero,List.prod_nil,Finset.univ_eq_empty,Finset.sum_empty]; exact (oddP% p_zero) ι |>.symm
  | succ M ih =>
    rw [orderedProduct,List.ofFn_succ,List.prod_cons]
    change p ι 0 (B 0)*orderedProduct (fun j => p ι 0 (B j.succ))=_
    rw [ih,central_add,Fin.sum_univ_succ]
private theorem central_value (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fˣ) (ha : ι (a:F)=(a:F)) (s : ℕ)
    (B : Matrix (Fin d) (Fin d) F) :
    (p ι 0 B)⁻¹*(action a phi^s) (p ι 0 B)=
      p ι 0 (fun i j => fieldValue phi 1 s 2 (a:F) (B i j)) := by
  rw [action_power_p ι phi hinv hne a ha,actual_p_inverse,actual_p_multiply]
  congr 1
  · funext i; simp
  · ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.of_apply,
      Pi.zero_apply,Pi.neg_apply,map_zero,mul_zero,zero_mul,fieldValue,one_mul]
    ring
private theorem constraint_zero_iff (ι : RingAut F) (B : Matrix (Fin d) (Fin d) F) :
    Constraint ι (0:Fin d → F) B ↔ PartIIUnitaryEvenP.Skew ι B := by
  constructor
  · intro h i j
    have hh := h i j
    simp only [Pi.zero_apply,mul_zero,zero_mul,add_zero] at hh
    linear_combination hh
  · intro h i j
    simp only [h i j,Pi.zero_apply,zero_mul,add_neg_cancel,add_zero]

private theorem central_two_batch {q M : ℕ} (hq : 0<q)
    (hM : q*(2*q+1)<M) (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi0 phi1 : Fin M → RingAut F) (s0 s1 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q) :
    ∃ a0 a1 : Fin M → Fˣ,
      (∀ j, ι (a0 j:F)=(a0 j:F) ∧ ι (a1 j:F)=(a1 j:F)) ∧
      ∀ B : Matrix (Fin d) (Fin d) F, PartIIUnitaryEvenP.Skew ι B →
        ∃ x0 x1 : Fin M → SpecialLinearGroup (Fin (2*d+1)) F,
          (∀ j, LayerDepth 1 ((x0 j).val-1) ∧ steinberg ι (x0 j)=x0 j ∧
            LayerDepth 1 ((x1 j).val-1) ∧ steinberg ι (x1 j)=x1 j) ∧
          values a0 phi0 s0 x0*values a1 phi1 s1 x1=p ι 0 B := by
  classical
  obtain ⟨b0,b1,hb,hcover⟩ := PartIIUnitaryEvenPProduct.actual_skew_two_batch (d:=d)
    hq hM ι hinv hne hK phi0 phi1 s0 s1 hs0 hs1
  let a0 := fun j => liftUnit ι (b0 j) (hb j).1
  let a1 := fun j => liftUnit ι (b1 j) (hb j).2
  have ha0 : ∀ j, ι (a0 j:F)=(a0 j:F) := fun j => (mem_fixedField ι (b0 j:F)).mp (b0 j).prop
  have ha1 : ∀ j, ι (a1 j:F)=(a1 j:F) := fun j => (mem_fixedField ι (b1 j:F)).mp (b1 j).prop
  refine ⟨a0,a1,fun j => ⟨ha0 j,ha1 j⟩,?_⟩
  intro B hB
  obtain ⟨T0,T1,hT,he⟩ := hcover B hB
  let x0 := fun j => p ι 0 (T0 j)
  let x1 := fun j => p ι 0 (T1 j)
  refine ⟨x0,x1,fun j => ⟨actual_p_upper _ _ _,
    (actual_p_unitary_iff ι hinv 0 _).mpr ((constraint_zero_iff ι _).mpr (hT j).1),
    actual_p_upper _ _ _,(actual_p_unitary_iff ι hinv 0 _).mpr ((constraint_zero_iff ι _).mpr (hT j).2)⟩,?_⟩
  have hv0 : ∀ j, (x0 j)⁻¹*(action (a0 j) (phi0 j)^s0 j) (x0 j)=
      p ι 0 (fun r c => fieldValue (phi0 j) 1 (s0 j) 2 (b0 j:F) (T0 j r c)) := by
    intro j
    simpa only [x0,a0,liftUnit,Units.val_mk0] using central_value ι (phi0 j) hinv hne (a0 j) (ha0 j) (s0 j) (T0 j)
  have hv1 : ∀ j, (x1 j)⁻¹*(action (a1 j) (phi1 j)^s1 j) (x1 j)=
      p ι 0 (fun r c => fieldValue (phi1 j) 1 (s1 j) 2 (b1 j:F) (T1 j r c)) := by
    intro j
    simpa only [x1,a1,liftUnit,Units.val_mk0] using central_value ι (phi1 j) hinv hne (a1 j) (ha1 j) (s1 j) (T1 j)
  have he0 : values a0 phi0 s0 x0=p ι 0 (∑ j, fun r c => fieldValue (phi0 j) 1 (s0 j) 2 (b0 j:F) (T0 j r c)) := by
    simp only [values,hv0]
    exact ordered_central ι _
  have he1 : values a1 phi1 s1 x1=p ι 0 (∑ j, fun r c => fieldValue (phi1 j) 1 (s1 j) 2 (b1 j:F) (T1 j r c)) := by
    simp only [values,hv1]
    exact ordered_central ι _
  rw [he0,he1,central_add,he]

/-- Full genuine odd-dimensional P FIELD PRODUCT, PartII pp271–272.
All FOUR fixed-field inner correction batches precede ALL true P
vector/central targets. The actual quotient witnesses, trace lifts,
noncommutative residual, positive/unitary constraints and original
positive divisor powers are consumed; no coverage/scalar oracle remains. -/
theorem actual_odd_P_field_four_batch {q M : ℕ} (hq : 0<q)
    (hM : q*(2*q+1)<M) (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (phi0 phi1 phi2 phi3 : Fin M → RingAut F) (s0 s1 s2 s3 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q)
    (hs2 : ∀ j, 0<s2 j ∧ s2 j∣q) (hs3 : ∀ j, 0<s3 j ∧ s3 j∣q) :
    ∃ h0 h1 h2 h3 : Fin M → SpecialLinearGroup (Fin (2*d+1)) F,
      (∀ j i l, i≠l → h0 j i l=0 ∧ h1 j i l=0 ∧ h2 j i l=0 ∧ h3 j i l=0) ∧
      (∀ j, steinberg ι (h0 j)=h0 j ∧ steinberg ι (h1 j)=h1 j ∧
        steinberg ι (h2 j)=h2 j ∧ steinberg ι (h3 j)=h3 j) ∧
      ∀ v : Fin d → F, ∀ B : Matrix (Fin d) (Fin d) F, Constraint ι v B →
        ∃ x0 x1 x2 x3 : Fin M → SpecialLinearGroup (Fin (2*d+1)) F,
          (∀ j, LayerDepth 1 ((x0 j).val-1) ∧ steinberg ι (x0 j)=x0 j ∧
            LayerDepth 1 ((x1 j).val-1) ∧ steinberg ι (x1 j)=x1 j ∧
            LayerDepth 1 ((x2 j).val-1) ∧ steinberg ι (x2 j)=x2 j ∧
            LayerDepth 1 ((x3 j).val-1) ∧ steinberg ι (x3 j)=x3 j) ∧
          orderedProduct (fun j => (x0 j)⁻¹*((MulAut.conj (h0 j)*fieldAut (n:=2*d+1) (phi0 j))^(s0 j)) (x0 j))*
          orderedProduct (fun j => (x1 j)⁻¹*((MulAut.conj (h1 j)*fieldAut (n:=2*d+1) (phi1 j))^(s1 j)) (x1 j))*
          orderedProduct (fun j => (x2 j)⁻¹*((MulAut.conj (h2 j)*fieldAut (n:=2*d+1) (phi2 j))^(s2 j)) (x2 j))*
          orderedProduct (fun j => (x3 j)⁻¹*((MulAut.conj (h3 j)*fieldAut (n:=2*d+1) (phi3 j))^(s3 j)) (x3 j))=p ι v B := by
  obtain ⟨a0,a1,ha01,hh01,hvector⟩ := actual_odd_P_vector_two_batch (d:=d)
    hq hM ι hinv hne hK phi0 phi1 s0 s1 hs0 hs1
  obtain ⟨a2,a3,ha23,hcentral⟩ := central_two_batch (d:=d)
    hq hM ι hinv hne hK phi2 phi3 s2 s3 hs2 hs3
  refine ⟨fun j => torus (a0 j),fun j => torus (a1 j),fun j => torus (a2 j),fun j => torus (a3 j),
    fun j i l hil => ⟨torus_diagonal _ _ _ hil,torus_diagonal _ _ _ hil,torus_diagonal _ _ _ hil,torus_diagonal _ _ _ hil⟩,
    fun j => ⟨(hh01 j).1,(hh01 j).2,torus_unitary ι hinv _ (ha23 j).1,
      torus_unitary ι hinv _ (ha23 j).2⟩,?_⟩
  intro v B hB
  obtain ⟨x0,x1,C,hx01,hC,he01⟩ := hvector v
  have hres : PartIIUnitaryEvenP.Skew ι (B-C) := by
    intro i j
    change ι (B j i-C j i)= -(B i j-C i j)
    rw [map_sub]
    linear_combination (hB i j)-(hC i j)
  obtain ⟨x2,x3,hx23,he23⟩ := hcentral (B-C) hres
  refine ⟨x0,x1,x2,x3,fun j => ⟨(hx01 j).1,(hx01 j).2.1,(hx01 j).2.2.1,(hx01 j).2.2.2,
    (hx23 j).1,(hx23 j).2.1,(hx23 j).2.2.1,(hx23 j).2.2.2⟩,?_⟩
  change values a0 phi0 s0 x0*values a1 phi1 s1 x1*values a2 phi2 s2 x2*values a3 phi3 s3 x3=_
  rw [mul_assoc (values a0 phi0 s0 x0*values a1 phi1 s1 x1),he01,he23,actual_p_multiply]
  congr 1
  · exact add_zero v
  · ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.of_apply,Pi.zero_apply,map_zero,mul_zero]
    ring

/-- All odd ranks and fields: chosen N(q),C(q) precede every FIELD tuple;
actual determinant-one diagonal UNITARY h precedes every true P target.
Ordered exact-length original positive-divisor commutator VALUES. -/
theorem actual_uniform_odd_P_field_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ),
      (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+1)) F,
        (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
        ∀ v : Fin d → F, ∀ B : Matrix (Fin d) (Fin d) F, Constraint ι v B →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d+1)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*((MulAut.conj (h j)*fieldAut (n:=2*d+1) (phi j))^(s j)) (x j))=p ι v B := by
  classical
  let M := q*(2*q+1)+1
  let K := 2*(2*q+1)^q
  refine ⟨M+M+M+M,K^2,by dsimp only [M]; omega,?_⟩
  intro F _ _ _ hF ι hinv hne d phi s hs
  have hK : K<Nat.card (fixedField ι) := by
    have hc := card_field ι hinv hne
    have hl : K^2<Nat.card F := by simpa only [Nat.card_eq_fintype_card] using hF
    rw [hc] at hl
    nlinarith
  let i0 := fun j : Fin M => ((j.castAdd M).castAdd M).castAdd M
  let i1 := fun j : Fin M => ((j.natAdd M).castAdd M).castAdd M
  let i2 := fun j : Fin M => (j.natAdd (M+M)).castAdd M
  let i3 := fun j : Fin M => j.natAdd (M+M+M)
  obtain ⟨h0,h1,h2,h3,hd,hh,hcover⟩ := actual_odd_P_field_four_batch (d:=d) hq
    (by dsimp only [M]; omega) ι hinv hne hK
    (fun j => phi (i0 j)) (fun j => phi (i1 j)) (fun j => phi (i2 j)) (fun j => phi (i3 j))
    (fun j => s (i0 j)) (fun j => s (i1 j)) (fun j => s (i2 j)) (fun j => s (i3 j))
    (fun j => hs _) (fun j => hs _) (fun j => hs _) (fun j => hs _)
  let h := Fin.append (Fin.append (Fin.append h0 h1) h2) h3
  have hhu : ∀ j, steinberg ι (h j)=h j := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [h,Fin.append_left] using (hh j).1
        · simpa only [h,Fin.append_left,Fin.append_right] using (hh j).2.1
      · simpa only [h,Fin.append_left,Fin.append_right] using (hh j).2.2.1
    · simpa only [h,Fin.append_right] using (hh j).2.2.2
  have hdiagonal : ∀ j i l, i≠l → h j i l=0 := by
    intro j i l hil
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [h,Fin.append_left] using (hd j i l hil).1
        · simpa only [h,Fin.append_left,Fin.append_right] using (hd j i l hil).2.1
      · simpa only [h,Fin.append_left,Fin.append_right] using (hd j i l hil).2.2.1
    · simpa only [h,Fin.append_right] using (hd j i l hil).2.2.2
  refine ⟨h,hdiagonal,hhu,?_⟩
  intro v B hB
  obtain ⟨x0,x1,x2,x3,hx,he⟩ := hcover v B hB
  have hx' : ∀ j, (LayerDepth 1 ((x0 j).val-1) ∧ steinberg ι (x0 j)=x0 j) ∧
      (LayerDepth 1 ((x1 j).val-1) ∧ steinberg ι (x1 j)=x1 j) ∧
      (LayerDepth 1 ((x2 j).val-1) ∧ steinberg ι (x2 j)=x2 j) ∧
      (LayerDepth 1 ((x3 j).val-1) ∧ steinberg ι (x3 j)=x3 j) := by
    intro j; exact ⟨⟨(hx j).1,(hx j).2.1⟩,⟨(hx j).2.2.1,(hx j).2.2.2.1⟩,
      ⟨(hx j).2.2.2.2.1,(hx j).2.2.2.2.2.1⟩,⟨(hx j).2.2.2.2.2.2.1,(hx j).2.2.2.2.2.2.2⟩⟩
  let x := Fin.append (Fin.append (Fin.append x0 x1) x2) x3
  refine ⟨x,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [x,Fin.append_left] using (hx' j).1
        · simpa only [x,Fin.append_left,Fin.append_right] using (hx' j).2.1
      · simpa only [x,Fin.append_left,Fin.append_right] using (hx' j).2.2.1
    · simpa only [x,Fin.append_right] using (hx' j).2.2.2
  · let v0 := fun j => (x0 j)⁻¹*((MulAut.conj (h0 j)*fieldAut (n:=2*d+1) (phi (i0 j)))^(s (i0 j))) (x0 j)
    let v1 := fun j => (x1 j)⁻¹*((MulAut.conj (h1 j)*fieldAut (n:=2*d+1) (phi (i1 j)))^(s (i1 j))) (x1 j)
    let v2 := fun j => (x2 j)⁻¹*((MulAut.conj (h2 j)*fieldAut (n:=2*d+1) (phi (i2 j)))^(s (i2 j))) (x2 j)
    let v3 := fun j => (x3 j)⁻¹*((MulAut.conj (h3 j)*fieldAut (n:=2*d+1) (phi (i3 j)))^(s (i3 j))) (x3 j)
    have hv : (fun j => (x j)⁻¹*((MulAut.conj (h j)*fieldAut (n:=2*d+1) (phi j))^(s j)) (x j))=
        Fin.append (Fin.append (Fin.append v0 v1) v2) v3 := by
      funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [x,h,Fin.append_left,v0,i0]
          · simp only [x,h,Fin.append_left,Fin.append_right,v1,i1]
        · simp only [x,h,Fin.append_left,Fin.append_right,v2,i2]
      · simp only [x,h,Fin.append_right,v3,i3]
    rw [hv]
    simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append] using he

end NikolovSegal.PartIIUnitaryOddPProduct
