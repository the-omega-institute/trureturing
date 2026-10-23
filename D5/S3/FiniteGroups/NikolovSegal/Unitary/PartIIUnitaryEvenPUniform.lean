/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPUniform
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPUniform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryEvenPProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Prescribed unitary diagonal/field tuples, pp255,271–272. The
ambient central H cancels the given diagonal BEFORE targets. Actual
relative-field P products are then transported without changing powers
or witnesses. The chosen length and field cutoff depend ONLY on q. -/
namespace NikolovSegal.PartIIUnitaryEvenPUniform
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIUnitaryUpperTorus PartIIUnitaryEvenP PartIIUnitaryEvenPProduct
open PartIIUnitaryTypeALeviProduct UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d M : ℕ}

private theorem cancel_diagonal (w : Fin (2*d) → Fˣ)
    (g : SpecialLinearGroup (Fin (2*d)) F) :
    (unitOdd% diagonalAut) (fun i => (w i)⁻¹) ((unitOdd% diagonalAut) w g)=g := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [unitOdd% diagonal_entry,unitOdd% diagonal_entry]
  simp only [inv_inv,Units.val_inv_eq_inv_val]
  field_simp

private theorem actual_cancel_prescribed_diagonal (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F) (a : Fin d → Fˣ) :
    ∃ h : SpecialLinearGroup (Fin (2*d+2)) F, steinberg ι h=h ∧
      ∀ phi : RingAut F, ∀ g : SpecialLinearGroup (Fin (2*d)) F,
        (MulAut.conj h) (diagonalField ι a phi (PartIICentralLevi.embed g))=
          PartIICentralLevi.embed (fieldAut phi g) := by
  let w := (unitaryTypeA% pairedUnits) ι a
  have hw : ∀ i, ι ((w i)⁻¹:Fˣ)*(((w i.rev)⁻¹:Fˣ):F)=1 := by
    intro i
    simp only [Units.val_inv_eq_inv_val,map_inv₀]
    rw [← mul_inv,(unitaryTypeA% pairedUnits_unitary) ι hinv a i,inv_one]
  obtain ⟨h,_,hhu,hact⟩ := PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
    ι hinv hne (fun i => (w i)⁻¹) 1 hw
  refine ⟨h,hhu,?_⟩
  intro phi g
  change (MulAut.conj h) ((unitOdd% diagonalAut) ((unitaryCentral% extendWeights) ι w 1)
    (fieldAut phi (PartIICentralLevi.embed g)))=_
  rw [centralKernel% field_embed,centralKernel% diagonal_embed]
  have he : (fun i => (unitaryCentral% extendWeights) ι w 1 (PartIICentralLevi.middle i))=w :=
    funext ((unitaryCentral% extend_middle) ι w 1)
  rw [he,hact,cancel_diagonal]

/-- Arbitrary genuine paired diagonal/field P tuples. Their ONE ambient
unitary INNER correction is constructed BEFORE every P target. -/
theorem actual_even_P_prescribed_two_batch {q : ℕ} (hq : 0<q) (hM : q*(2*q+1)<M)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (a0 a1 : Fin M → Fin d → Fˣ) (phi0 phi1 : Fin M → RingAut F) (s0 s1 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q) :
    ∃ h0 h1 : Fin M → SpecialLinearGroup (Fin (2*d+2)) F,
      (∀ j, steinberg ι (h0 j)=h0 j ∧ steinberg ι (h1 j)=h1 j) ∧
      ∀ B : Matrix (Fin d) (Fin d) F, Skew ι B →
        ∃ T0 T1 : Fin M → Matrix (Fin d) (Fin d) F,
          (∀ j, Skew ι (T0 j) ∧ Skew ι (T1 j)) ∧
          NikolovSegal.orderedProduct (fun j => (PartIICentralLevi.embed (p (T0 j)))⁻¹*
            ((MulAut.conj (h0 j)*diagonalField ι (a0 j) (phi0 j))^(s0 j)) (PartIICentralLevi.embed (p (T0 j))))*
          NikolovSegal.orderedProduct (fun j => (PartIICentralLevi.embed (p (T1 j)))⁻¹*
            ((MulAut.conj (h1 j)*diagonalField ι (a1 j) (phi1 j))^(s1 j)) (PartIICentralLevi.embed (p (T1 j))))=
          PartIICentralLevi.embed (p B) := by
  classical
  obtain ⟨h0,h1,hh,hclosed,hcover⟩ := actual_even_P_two_batch_inner_product (d:=d) hq hM ι hinv hne hK phi0 phi1 s0 s1 hs0 hs1
  have hC0 := fun j => actual_cancel_prescribed_diagonal ι hinv hne (a0 j)
  have hC1 := fun j => actual_cancel_prescribed_diagonal ι hinv hne (a1 j)
  choose c0 hc0 hact0 using hC0
  choose c1 hc1 hact1 using hC1
  have hp : ∀ (h c : SpecialLinearGroup (Fin (2*d+2)) F) (a : Fin d → Fˣ) (phi : RingAut F),
      (∀ g : SpecialLinearGroup (Fin (2*d)) F,
        (MulAut.conj c) (diagonalField ι a phi (PartIICentralLevi.embed g))=
          PartIICentralLevi.embed (fieldAut phi g)) →
      (∀ g : SpecialLinearGroup (Fin (2*d)) F, ∃ z : SpecialLinearGroup (Fin (2*d)) F,
        (MulAut.conj h) (PartIICentralLevi.embed g)=PartIICentralLevi.embed z) →
      ∀ s : ℕ, ∀ g : SpecialLinearGroup (Fin (2*d)) F,
        ((MulAut.conj (h*c)*diagonalField ι a phi)^s) (PartIICentralLevi.embed g)=
          ((MulAut.conj h*fieldAut (n:=2*d+2) phi)^s) (PartIICentralLevi.embed g) := by
    intro h c a phi hc hclosed s
    have step : ∀ g : SpecialLinearGroup (Fin (2*d)) F,
        (MulAut.conj (h*c)*diagonalField ι a phi) (PartIICentralLevi.embed g)=
          (MulAut.conj h*fieldAut (n:=2*d+2) phi) (PartIICentralLevi.embed g) := by
      intro g
      rw [map_mul,MulAut.mul_apply,MulAut.mul_apply,hc,MulAut.mul_apply,centralKernel% field_embed]
    -- The power induction uses the unchanged central action, not a
    -- false global equality of the two ambient automorphisms.
    intro g
    have closed : ∀ t : ℕ, ∃ z : SpecialLinearGroup (Fin (2*d)) F,
        ((MulAut.conj h*fieldAut (n:=2*d+2) phi)^t) (PartIICentralLevi.embed g)=PartIICentralLevi.embed z := by
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
  refine ⟨fun j => h0 j*c0 j,fun j => h1 j*c1 j,?_,?_⟩
  · intro j
    simp only [map_mul,(hh j).1,(hh j).2,hc0 j,hc1 j]
    trivial
  · intro B hB
    obtain ⟨T0,T1,hT,he⟩ := hcover B hB
    refine ⟨T0,T1,hT,?_⟩
    simp only [hp _ _ _ _ (hact0 _ _) (fun g => (hclosed _ g).1),
      hp _ _ _ _ (hact1 _ _) (fun g => (hclosed _ g).2)]
    exact he

/-- Chosen-length, all-rank EVEN P Proposition6.10 branch. N(q) and the
FIELD cutoff are fixed before every field/rank/prescribed tuple. ONE
ambient inner correction is fixed before ALL actual P targets; the
witnesses are positive UNITARY ambient matrices, and values are ordered. -/
theorem actual_uniform_even_P_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin d → Fˣ) (phi : Fin N → RingAut F)
        (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ B : Matrix (Fin d) (Fin d) F, Skew ι B →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            NikolovSegal.orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (x j))=
              PartIICentralLevi.embed (p B) := by
  classical
  let M := q*(2*q+1)+1
  let K := 2*(2*q+1)^q
  refine ⟨M+M,K^2,by dsimp only [M]; omega,?_⟩
  intro F _ _ _ hF ι hinv hne d a phi s hs
  have hK : K<Nat.card (fixedField ι) := by
    have hc := card_field ι hinv hne
    have hlarge : K^2<Nat.card F := by simpa only [Nat.card_eq_fintype_card] using hF
    rw [hc] at hlarge
    nlinarith
  obtain ⟨h0,h1,hh,hcover⟩ := actual_even_P_prescribed_two_batch (d:=d) hq
    (by dsimp only [M]; omega) ι hinv hne hK
    (fun j => a (j.castAdd M)) (fun j => a (j.natAdd M))
    (fun j => phi (j.castAdd M)) (fun j => phi (j.natAdd M))
    (fun j => s (j.castAdd M)) (fun j => s (j.natAdd M))
    (fun j => hs _) (fun j => hs _)
  let h := Fin.append h0 h1
  refine ⟨h,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [h,Fin.append_left] using (hh j).1
    · simpa only [h,Fin.append_right] using (hh j).2
  · intro B hB
    obtain ⟨T0,T1,hT,he⟩ := hcover B hB
    let x0 := fun j => PartIICentralLevi.embed (p (T0 j))
    let x1 := fun j => PartIICentralLevi.embed (p (T1 j))
    let x := Fin.append x0 x1
    have hx0 : ∀ j, LayerDepth 1 ((x0 j).val-1) ∧ steinberg ι (x0 j)=x0 j := by
      intro j
      refine ⟨PartIIAmbientUnipotentDecomposition.actual_central_embed_unitriangular _ (actual_p_upper _),?_⟩
      rw [PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,
        (actual_p_unitary_iff ι _).mpr (hT j).1]
    have hx1 : ∀ j, LayerDepth 1 ((x1 j).val-1) ∧ steinberg ι (x1 j)=x1 j := by
      intro j
      refine ⟨PartIIAmbientUnipotentDecomposition.actual_central_embed_unitriangular _ (actual_p_upper _),?_⟩
      rw [PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,
        (actual_p_unitary_iff ι _).mpr (hT j).2]
    refine ⟨x,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [x,Fin.append_left] using hx0 j
      · simpa only [x,Fin.append_right] using hx1 j
    · let v0 := fun j => (x0 j)⁻¹*((MulAut.conj (h0 j)*diagonalField ι (a (j.castAdd M)) (phi (j.castAdd M)))^(s (j.castAdd M))) (x0 j)
      let v1 := fun j => (x1 j)⁻¹*((MulAut.conj (h1 j)*diagonalField ι (a (j.natAdd M)) (phi (j.natAdd M)))^(s (j.natAdd M))) (x1 j)
      have hv : (fun j => (x j)⁻¹*((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (x j))=Fin.append v0 v1 := by
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,h,Fin.append_left,v0]
        · simp only [x,h,Fin.append_right,v1]
      rw [hv]
      simpa only [NikolovSegal.orderedProduct,List.ofFn_fin_append,List.prod_append,v0,v1,x0,x1] using he
end NikolovSegal.PartIIUnitaryEvenPUniform
