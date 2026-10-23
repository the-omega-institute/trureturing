/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryGeneralEvenUProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryGeneralEvenUProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryAmbientOddUProduct
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII printed p255, Case2: the actual EVEN central U1=U2 P,
for arbitrary genuine prescribed diagonal-similitude/field tuples.
The accepted even decomposition and actual q-power action are consumed. -/
namespace NikolovSegal.PartIIUnitaryGeneralEvenUProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open PartIIUnitaryTypeALevi UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}
private abbrev levi (ι : RingAut F) : SpecialLinearGroup (Fin d) F →*
    SpecialLinearGroup (Fin (2*d+2)) F := PartIIUnitaryTypeALeviProduct.levi ι
private theorem levi_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin d) F) : steinberg ι (levi ι g)=levi ι g := by
  change steinberg ι (PartIICentralLevi.embed (embed ι g))=_
  rw [PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,actual_typeA_levi_unitary ι hinv]
  rfl

/-- Actual type-A PRODUCT on the central even Levi. The entire prescribed
D action is cancelled on ALL central elements; both scalar corrections
and ONE ambient SU inner tuple precede all positive type-A targets. -/
theorem actual_uniform_even_Levi_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin (2*d+2) → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin d) F, LayerDepth 1 (b.val-1) →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (PartIICentralLevi.embed (x j))⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j))
                (PartIICentralLevi.embed (x j)))=levi ι b := by
  classical
  obtain ⟨N,C,hN,hA⟩ := PartIIProposition6_5.actual_proposition6_5_uniform_diagonal_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne d a c ha phi s hs
  obtain ⟨eta,u,hu,hcover⟩ := hA F hF d (fun _ _ => 1) phi (fun _ => false) s hs
  have hD := fun j => actual_typeA_levi_ambient_diagonal_inner ι hinv hne (eta j)
  choose hD hhD heD using hD
  let w : Fin N → Fin (2*d) → Fˣ := fun j i => a j (PartIICentralLevi.middle i)
  have hw : ∀ j i, ι (((w j i)⁻¹:Fˣ):F)*(((w j i.rev)⁻¹:Fˣ):F)=(((c j)⁻¹: (fixedField ι)ˣ):fixedField ι) := by
    intro j i
    simp only [Units.val_inv_eq_inv_val,map_inv₀]
    rw [← mul_inv]
    have hr : (PartIICentralLevi.middle i).rev=PartIICentralLevi.middle i.rev := (centralKernel% rev_middle) i
    have h := ha j (PartIICentralLevi.middle i)
    rw [hr] at h
    rw [show ι (w j i:F)*(w j i.rev:F)=((c j:fixedField ι):F) from h]
    rfl
  have hC := fun j => PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
    ι hinv hne (fun i => (w j i)⁻¹) (c j)⁻¹ (hw j)
  choose hC hdC hhC heC using hC
  let h := fun j => levi ι (u j)*hD j*hC j
  let alpha := fun j => MulAut.conj (u j)*(unitOdd% diagonalAut) (eta j)*
    PartIIProposition6_5.diagonalFieldGraph (fun _ => 1) (phi j) false
  let beta := fun j => MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false
  have step : ∀ j g, beta j (levi ι g)=levi ι (alpha j g) := by
    intro j g
    have cancel : (unitOdd% diagonalAut) (fun i => (w j i)⁻¹)
        ((unitOdd% diagonalAut) (w j) (fieldAut (phi j) (embed ι g)))=fieldAut (phi j) (embed ι g) :=
      ((unitOdd% diagonalAut) (w j)).left_inv _
    change (MulAut.conj (h j)) ((unitOdd% diagonalAut) (a j)
      (fieldAut (phi j) (PartIICentralLevi.embed (embed ι g))))=_
    rw [centralKernel% field_embed,centralKernel% diagonal_embed]
    dsimp only [h]
    rw [map_mul,map_mul,MulAut.mul_apply,MulAut.mul_apply,heC j,cancel,
      actual_typeA_levi_field_action ι (phi j) hinv hne,heD j]
    have hone : ∀ g : SpecialLinearGroup (Fin d) F,
        PartIIProposition6_5.diagonalFieldGraph (fun _ => 1) (phi j) false g=fieldAut (phi j) g := by
      intro g
      apply SpecialLinearGroup.ext
      intro i l
      change ((unitOdd% diagonalAut) (fun _ : Fin d => (1:Fˣ)) (fieldAut (phi j) g)) i l=_
      rw [unitOdd% diagonal_entry]; simp
    simp only [alpha,MulAut.mul_apply,hone,MulAut.conj_apply,levi,PartIIUnitaryTypeALeviProduct.levi,MonoidHom.comp_apply,map_mul,map_inv]
  have power : ∀ j t g, (beta j^t) (levi ι g)=levi ι ((alpha j^t) g) := by
    intro j t
    induction t with
    | zero => intro g; rfl
    | succ t ih => intro g; rw [pow_succ',MulAut.mul_apply,ih,step,pow_succ',MulAut.mul_apply]; rfl
  refine ⟨h,?_,?_⟩
  · intro j
    dsimp only [h]
    rw [map_mul,map_mul,levi_unitary ι hinv,hhD j,hhC j]
  · intro b hb
    obtain ⟨z,hz,he⟩ := hcover b hb
    refine ⟨fun j => embed ι (z j),fun j =>
      ⟨(actual_typeA_levi_upper ι hinv _ (hz j)).1,actual_typeA_levi_unitary ι hinv _⟩,?_⟩
    change orderedProduct (fun j => (levi ι (z j))⁻¹*(beta j^(s j)) (levi ι (z j)))=levi ι b
    simp only [power,← map_inv,← map_mul]
    have hh := congrArg (fun g => levi ι g) he
    simpa only [alpha,orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def] using hh

private theorem cancel_power {n : ℕ}
    (h c : SpecialLinearGroup (Fin (n+2)) F) (a : Fin (n+2) → Fˣ) (phi : RingAut F)
    (hc : ∀ g : SpecialLinearGroup (Fin n) F,
      (MulAut.conj c) (PartIIProposition6_5.diagonalFieldGraph a phi false (PartIICentralLevi.embed g))=
        PartIICentralLevi.embed (fieldAut phi g))
    (hclosed : ∀ g : SpecialLinearGroup (Fin n) F, ∃ z : SpecialLinearGroup (Fin n) F,
      (MulAut.conj h) (PartIICentralLevi.embed g)=PartIICentralLevi.embed z)
    (s : ℕ) (g : SpecialLinearGroup (Fin n) F) :
    ((MulAut.conj (h*c)*PartIIProposition6_5.diagonalFieldGraph a phi false)^s) (PartIICentralLevi.embed g)=
      ((MulAut.conj h*fieldAut (n:=n+2) phi)^s) (PartIICentralLevi.embed g) := by
  have step : ∀ g : SpecialLinearGroup (Fin n) F,
      (MulAut.conj (h*c)*PartIIProposition6_5.diagonalFieldGraph a phi false) (PartIICentralLevi.embed g)=
        (MulAut.conj h*fieldAut (n:=n+2) phi) (PartIICentralLevi.embed g) := by
    intro g
    rw [map_mul,MulAut.mul_apply,MulAut.mul_apply,hc,MulAut.mul_apply,centralKernel% field_embed]
  have closed : ∀ t : ℕ, ∃ z : SpecialLinearGroup (Fin n) F,
      ((MulAut.conj h*fieldAut (n:=n+2) phi)^t) (PartIICentralLevi.embed g)=PartIICentralLevi.embed z := by
    intro t
    induction t with
    | zero => exact ⟨g,rfl⟩
    | succ t ih =>
      obtain ⟨z,hz⟩ := ih
      obtain ⟨w,hw⟩ := hclosed (fieldAut phi z)
      exact ⟨w,by rw [pow_succ',MulAut.mul_apply,hz,MulAut.mul_apply,centralKernel% field_embed,hw]⟩
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ',MulAut.mul_apply,ih]
    obtain ⟨z,hz⟩ := closed s
    rw [hz,step,← hz,pow_succ',MulAut.mul_apply]
    rfl

/-- General diagonal-similitude/field even P PRODUCT. Real scalar/skew
witnesses and exact central powers are transported; ONE ambient unitary
inner tuple precedes every actual skew target. -/
theorem actual_uniform_even_P_general_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin (2*d+2) → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ B : Matrix (Fin d) (Fin d) F, PartIIUnitaryEvenP.Skew ι B →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (PartIICentralLevi.embed (x j))⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j))
                (PartIICentralLevi.embed (x j)))=PartIICentralLevi.embed (PartIIUnitaryEvenP.p B) := by
  classical
  let M := q*(2*q+1)+1
  let K := 2*(2*q+1)^q
  refine ⟨M+M,K^2,by dsimp only [M]; omega,?_⟩
  intro F _ _ _ hF ι hinv hne d a c ha phi s hs
  have hK : K<Nat.card (fixedField ι) := by
    have hc := card_field ι hinv hne
    have hl : K^2<Nat.card F := by simpa only [Nat.card_eq_fintype_card] using hF
    rw [hc] at hl
    nlinarith
  obtain ⟨h0,h1,hh,hclosed,hcover⟩ := PartIIUnitaryEvenPProduct.actual_even_P_two_batch_inner_product (d:=d)
    hq (by dsimp only [M]; omega) ι hinv hne hK
    (fun j => phi (j.castAdd M)) (fun j => phi (j.natAdd M))
    (fun j => s (j.castAdd M)) (fun j => s (j.natAdd M)) (fun j => hs _) (fun j => hs _)
  let w : Fin (M+M) → Fin (2*d) → Fˣ := fun j i => a j (PartIICentralLevi.middle i)
  have hw : ∀ j i, ι (((w j i)⁻¹:Fˣ):F)*(((w j i.rev)⁻¹:Fˣ):F)=(((c j)⁻¹: (fixedField ι)ˣ):fixedField ι) := by
    intro j i
    simp only [Units.val_inv_eq_inv_val,map_inv₀]
    rw [← mul_inv]
    have hr : (PartIICentralLevi.middle i).rev=PartIICentralLevi.middle i.rev := (centralKernel% rev_middle) i
    have h := ha j (PartIICentralLevi.middle i)
    rw [hr] at h
    rw [show ι (w j i:F)*(w j i.rev:F)=((c j:fixedField ι):F) from h]
    rfl
  have hC := fun j => PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
    ι hinv hne (fun i => (w j i)⁻¹) (c j)⁻¹ (hw j)
  choose hC hdC hhC heC using hC
  have cancel : ∀ j g, (MulAut.conj (hC j))
      (PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false (PartIICentralLevi.embed g))=
        PartIICentralLevi.embed (fieldAut (phi j) g) := by
    intro j g
    change (MulAut.conj (hC j)) ((unitOdd% diagonalAut) (a j) (fieldAut (phi j) (PartIICentralLevi.embed g)))=_
    rw [centralKernel% field_embed,centralKernel% diagonal_embed,heC j]
    have hc : (unitOdd% diagonalAut) (fun i => (w j i)⁻¹)
        ((unitOdd% diagonalAut) (w j) (fieldAut (phi j) g))=fieldAut (phi j) g :=
      ((unitOdd% diagonalAut) (w j)).left_inv _
    rw [hc]
  let h := Fin.append (fun j => h0 j*hC (j.castAdd M)) (fun j => h1 j*hC (j.natAdd M))
  refine ⟨h,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [h,Fin.append_left,map_mul,(hh j).1,hhC]
    · simp only [h,Fin.append_right,map_mul,(hh j).2,hhC]
  · intro B hB
    obtain ⟨T0,T1,hT,he⟩ := hcover B hB
    let x0 := fun j => PartIIUnitaryEvenP.p (T0 j)
    let x1 := fun j => PartIIUnitaryEvenP.p (T1 j)
    let x := Fin.append x0 x1
    refine ⟨x,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [x,x0,Fin.append_left] using
          ⟨PartIIUnitaryEvenP.actual_p_upper _,(PartIIUnitaryEvenP.actual_p_unitary_iff ι _).mpr (hT j).1⟩
      · simpa only [x,x1,Fin.append_right] using
          ⟨PartIIUnitaryEvenP.actual_p_upper _,(PartIIUnitaryEvenP.actual_p_unitary_iff ι _).mpr (hT j).2⟩
    · let v0 := fun j => (PartIICentralLevi.embed (x0 j))⁻¹*
        ((MulAut.conj (h0 j*hC (j.castAdd M))*PartIIProposition6_5.diagonalFieldGraph (a (j.castAdd M)) (phi (j.castAdd M)) false)^(s (j.castAdd M)))
          (PartIICentralLevi.embed (x0 j))
      let v1 := fun j => (PartIICentralLevi.embed (x1 j))⁻¹*
        ((MulAut.conj (h1 j*hC (j.natAdd M))*PartIIProposition6_5.diagonalFieldGraph (a (j.natAdd M)) (phi (j.natAdd M)) false)^(s (j.natAdd M)))
          (PartIICentralLevi.embed (x1 j))
      have he' : orderedProduct v0*orderedProduct v1=PartIICentralLevi.embed (PartIIUnitaryEvenP.p B) := by
        simp only [v0,v1,cancel_power _ _ _ _ (cancel _) (fun g => (hclosed _ g).1),
          cancel_power _ _ _ _ (cancel _) (fun g => (hclosed _ g).2)]
        exact he
      have hv : (fun j => (PartIICentralLevi.embed (x j))⁻¹*
        ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j))
          (PartIICentralLevi.embed (x j)))=Fin.append v0 v1 := by
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,h,Fin.append_left,v0]
        · simp only [x,h,Fin.append_right,v1]
      rw [hv]
      simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append] using he'
/-- The ENTIRE central even positive unitary U, with arbitrary genuine
prescribed D/Phi actions. Derived even U=U2 P and both actual suppliers
are consumed; ONE correction precedes ALL targets. -/
theorem actual_uniform_central_even_U_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin (2*d+2) → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin (2*d)) F,
          LayerDepth 1 (b.val-1) → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (PartIICentralLevi.embed (x j))⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j))
                (PartIICentralLevi.embed (x j)))=PartIICentralLevi.embed b := by
  classical
  obtain ⟨L,CL,hL,hLevi⟩ := actual_uniform_even_Levi_prescribed_product q hq
  obtain ⟨P,CP,hP,hComplement⟩ := actual_uniform_even_P_general_prescribed_product q hq
  refine ⟨L+P,max CL CP,by omega,?_⟩
  intro F _ _ _ hF ι hinv hne d a c ha phi s hs
  obtain ⟨h0,hh0,hcover0⟩ := hLevi F ((le_max_left _ _).trans_lt hF) ι hinv hne d
    (fun j => a (j.castAdd P)) (fun j => c (j.castAdd P)) (fun j => ha _)
    (fun j => phi (j.castAdd P)) (fun j => s (j.castAdd P)) (fun j => hs _)
  obtain ⟨h1,hh1,hcover1⟩ := hComplement F ((le_max_right _ _).trans_lt hF) ι hinv hne d
    (fun j => a (j.natAdd L)) (fun j => c (j.natAdd L)) (fun j => ha _)
    (fun j => phi (j.natAdd L)) (fun j => s (j.natAdd L)) (fun j => hs _)
  let h := Fin.append h0 h1
  refine ⟨h,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [h,Fin.append_left] using hh0 j
    · simpa only [h,Fin.append_right] using hh1 j
  · intro b hb hbu
    obtain ⟨g,B,hg,hB,hgB⟩ := PartIIUnitaryEvenP.actual_even_unitary_U_decomposition ι hinv b hb hbu
    obtain ⟨x0,hx0,he0⟩ := hcover0 g hg
    obtain ⟨x1,hx1,he1⟩ := hcover1 B hB
    let x := Fin.append x0 x1
    refine ⟨x,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [x,Fin.append_left] using hx0 j
      · simpa only [x,Fin.append_right] using hx1 j
    · let v0 := fun j => (PartIICentralLevi.embed (x0 j))⁻¹*
        ((MulAut.conj (h0 j)*PartIIProposition6_5.diagonalFieldGraph (a (j.castAdd P)) (phi (j.castAdd P)) false)^(s (j.castAdd P)))
          (PartIICentralLevi.embed (x0 j))
      let v1 := fun j => (PartIICentralLevi.embed (x1 j))⁻¹*
        ((MulAut.conj (h1 j)*PartIIProposition6_5.diagonalFieldGraph (a (j.natAdd L)) (phi (j.natAdd L)) false)^(s (j.natAdd L)))
          (PartIICentralLevi.embed (x1 j))
      have hv : (fun j => (PartIICentralLevi.embed (x j))⁻¹*
        ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j))
          (PartIICentralLevi.embed (x j)))=Fin.append v0 v1 := by
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,h,Fin.append_left,v0]
        · simp only [x,h,Fin.append_right,v1]
      rw [hv]
      have he : orderedProduct v0*orderedProduct v1=PartIICentralLevi.embed b := by
        rw [show orderedProduct v0=levi ι g from he0,
          show orderedProduct v1=PartIICentralLevi.embed (PartIIUnitaryEvenP.p B) from he1]
        change PartIICentralLevi.embed (embed ι g)*PartIICentralLevi.embed (PartIIUnitaryEvenP.p B)=_
        rw [← map_mul,hgB]
      simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append] using he
end NikolovSegal.PartIIUnitaryGeneralEvenUProduct
