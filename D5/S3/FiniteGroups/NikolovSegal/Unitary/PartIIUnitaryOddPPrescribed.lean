/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPPrescribed
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddPPrescribed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryOddPProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIUnitaryOddPPrescribed
open Matrix PartIIUnitaryOddP PartIIUnitaryOddPProduct PartIIUnitaryUpperTorus
open PartIIUnitriangularActions PartIIUnitriangularLayers UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}
private theorem cancel_diagonal {n : ℕ} (a : Fin n → Fˣ)
    (g : SpecialLinearGroup (Fin n) F) :
    (unitOdd% diagonalAut) (fun i => (a i)⁻¹) ((unitOdd% diagonalAut) a g)=g := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [unitOdd% diagonal_entry,unitOdd% diagonal_entry]
  simp only [inv_inv,Units.val_inv_eq_inv_val]
  field_simp
private theorem diagonal_mul {n : ℕ} (a b : SpecialLinearGroup (Fin n) F)
    (ha : ∀ i j, i≠j → a i j=0) (hb : ∀ i j, i≠j → b i j=0)
    (i j : Fin n) (hij : i≠j) : (a*b) i j=0 := by
  rw [SpecialLinearGroup.coe_mul,Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hi : i=t
  · subst t; rw [hb i j hij,mul_zero]
  · rw [ha i t hi,zero_mul]
private theorem embed_diagonal {n : ℕ} (g : SpecialLinearGroup (Fin n) F)
    (hg : ∀ i j, i≠j → g i j=0) (i j : Fin (n+2)) (hij : i≠j) :
    PartIICentralLevi.embed g i j=0 := by
  obtain ⟨i,rfl⟩ := (centralKernel% indexEquiv).surjective i
  obtain ⟨j,rfl⟩ := (centralKernel% indexEquiv).surjective j
  rw [centralKernel% entry]
  have hne : i≠j := fun he => hij (congrArg (centralKernel% indexEquiv) he)
  cases i with
  | inl i => cases j with
    | inl j => have he : i=j := Subsingleton.elim _ _; exact (hne (congrArg Sum.inl he)).elim
    | inr j => simp
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp
      | inr j => cases j with
        | inl j => exact hg i j (fun he => hne (congrArg (fun t => Sum.inr (Sum.inl t)) he))
        | inr j => simp
    | inr i => cases j with
      | inl j => simp
      | inr j => cases j with
        | inl j => simp
        | inr j => have he : i=j := Subsingleton.elim _ _; exact (hne (congrArg (fun t => Sum.inr (Sum.inr t)) he)).elim

/-- Actual general prescribed D/Phi actions on the central odd P.
The genuine ambient H canceller is constructed from the supplied
similitude weights; the scalar/product corrections and the SAME
ambient inner tuple precede ALL P targets. No whole-P cover is assumed. -/
theorem actual_uniform_central_odd_P_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin (2*d+1+2) → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+1+2)) F,
        (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
        ∀ v : Fin d → F, ∀ B : Matrix (Fin d) (Fin d) F, Constraint ι v B →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d+1)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (PartIICentralLevi.embed (x j))⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j))
                (PartIICentralLevi.embed (x j)))=PartIICentralLevi.embed (p ι v B) := by
  classical
  obtain ⟨N,C,hN,hfield⟩ := actual_uniform_odd_P_field_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne d a c ha phi s hs
  obtain ⟨h0,hd0,hh0,hcover⟩ := hfield F hF ι hinv hne d phi s hs
  let w : Fin N → Fin (2*d+1) → Fˣ := fun j i => a j (PartIICentralLevi.middle i)
  have hw : ∀ j i, ι (((w j i)⁻¹:Fˣ):F)*(((w j i.rev)⁻¹:Fˣ):F)=(((c j)⁻¹: (fixedField ι)ˣ):fixedField ι) := by
    intro j i
    simp only [Units.val_inv_eq_inv_val,map_inv₀]
    rw [← mul_inv]
    have hr : (PartIICentralLevi.middle i).rev=PartIICentralLevi.middle i.rev := (centralKernel% rev_middle) i
    have h := ha j (PartIICentralLevi.middle i)
    rw [hr] at h
    rw [show ι (w j i:F)*(w j i.rev:F)=((c j:fixedField ι):F) from h]
    rfl
  have hc := fun j => PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
    ι hinv hne (fun i => (w j i)⁻¹) (c j)⁻¹ (hw j)
  choose hC hdC hhC heC using hc
  let h := fun j => PartIICentralLevi.embed (h0 j)*hC j
  let alpha := fun j => MulAut.conj (h0 j)*fieldAut (n:=2*d+1) (phi j)
  let beta := fun j => MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false
  have step : ∀ j g, beta j (PartIICentralLevi.embed g)=PartIICentralLevi.embed (alpha j g) := by
    intro j g
    change (MulAut.conj (h j)) ((unitOdd% diagonalAut) (a j) (fieldAut (phi j) (PartIICentralLevi.embed g)))=_
    rw [centralKernel% field_embed,centralKernel% diagonal_embed]
    dsimp only [h]
    rw [map_mul,MulAut.mul_apply,heC j,cancel_diagonal]
    simp only [alpha,MulAut.mul_apply,MulAut.conj_apply,← map_inv,← map_mul]
  have power : ∀ j t g, (beta j^t) (PartIICentralLevi.embed g)=PartIICentralLevi.embed ((alpha j^t) g) := by
    intro j t
    induction t with
    | zero => intro g; rfl
    | succ t ih => intro g; rw [pow_succ',MulAut.mul_apply,ih,step,pow_succ',MulAut.mul_apply]; rfl
  refine ⟨h,?_,?_,?_⟩
  · intro j i l hil
    exact diagonal_mul _ _ (embed_diagonal _ (hd0 j)) (hdC j) i l hil
  · intro j
    dsimp only [h]
    rw [map_mul,PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,hh0 j,hhC j]
  · intro v B hB
    obtain ⟨x,hx,he⟩ := hcover v B hB
    refine ⟨x,hx,?_⟩
    change orderedProduct (fun j => (PartIICentralLevi.embed (x j))⁻¹*(beta j^(s j)) (PartIICentralLevi.embed (x j)))=_
    simp only [power,← map_inv,← map_mul]
    have hh := congrArg (fun g => PartIICentralLevi.embed g) he
    simpa only [alpha,orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def] using hh
end NikolovSegal.PartIIUnitaryOddPPrescribed
