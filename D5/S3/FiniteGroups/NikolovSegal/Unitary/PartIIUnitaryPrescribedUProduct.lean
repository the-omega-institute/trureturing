/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryPrescribedUProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryPrescribedUProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryAmbientGeneralEvenUProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII Proposition6.2, printed p255 Case2: a SINGLE chosen length
and field cutoff before every rank>=6 and every genuine prescribed
D/Phi tuple. Both actual parity reconstructions are consumed. -/
namespace NikolovSegal.PartIIUnitaryPrescribedUProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus UnitaryField
universe u
/-- Arbitrary-rank, arbitrary genuine prescribed diagonal-similitude/field
positive-U PRODUCT. The same fixed length and field cutoff cover BOTH
parities; ONE global SU correction is chosen BEFORE all targets. -/
theorem actual_uniform_all_rank_unitary_U_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin n) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin n) F,
          LayerDepth 1 (b.val-1) → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin n) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=b := by
  classical
  obtain ⟨E,CE,hE,heven⟩ := PartIIUnitaryAmbientGeneralEvenUProduct.actual_uniform_ambient_even_U_general_prescribed_product q hq
  obtain ⟨O,CO,hO,hodd⟩ := PartIIUnitaryAmbientOddUProduct.actual_uniform_ambient_odd_U_prescribed_product q hq
  refine ⟨E+O,max CE CO,by omega,?_⟩
  intro F _ _ _ hF ι hinv hne n hn
  have hcases : (∃ d, n=2*(d+2)+2) ∨ (∃ d, n=2*(d+2)+1+2) := by
    by_cases he : n%2=0
    · left; exact ⟨n/2-3,by omega⟩
    · right; exact ⟨n/2-3,by omega⟩
  rcases hcases with ⟨d,rfl⟩ | ⟨d,rfl⟩
  · intro a c ha phi s hs
    obtain ⟨h0,hh0,hcover⟩ := heven F ((le_max_left _ _).trans_lt hF) ι hinv hne d
      (fun j => a (j.castAdd O)) (fun j => c (j.castAdd O)) (fun j => ha _)
      (fun j => phi (j.castAdd O)) (fun j => s (j.castAdd O)) (fun j => hs _)
    let h := Fin.append h0 (fun _ : Fin O => 1)
    refine ⟨h,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [h,Fin.append_left] using hh0 j
      · simp only [h,Fin.append_right,map_one]
    · intro b hb hu
      obtain ⟨x0,hx0,he0⟩ := hcover b hb hu
      let x := Fin.append x0 (fun _ : Fin O => 1)
      refine ⟨x,?_,?_⟩
      · intro j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [x,Fin.append_left] using hx0 j
        · simp only [x,Fin.append_right,SpecialLinearGroup.coe_one,sub_self,map_one]
          exact ⟨fun _ _ _ => rfl,trivial⟩
      · let v0 := fun j => (x0 j)⁻¹*
          ((MulAut.conj (h0 j)*PartIIProposition6_5.diagonalFieldGraph (a (j.castAdd O)) (phi (j.castAdd O)) false)^(s (j.castAdd O))) (x0 j)
        have hv : (fun j => (x j)⁻¹*
          ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=
            Fin.append v0 (fun _ : Fin O => 1) := by
          funext j
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [x,h,Fin.append_left,v0]
          · simp only [x,h,Fin.append_right,inv_one,map_one,mul_one]
        rw [hv]
        simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append,List.ofFn_const,List.prod_replicate,one_pow,mul_one] using he0
  · intro a c ha phi s hs
    obtain ⟨h1,hh1,hcover⟩ := hodd F ((le_max_right _ _).trans_lt hF) ι hinv hne d
      (fun j => a (j.natAdd E)) (fun j => c (j.natAdd E)) (fun j => ha _)
      (fun j => phi (j.natAdd E)) (fun j => s (j.natAdd E)) (fun j => hs _)
    let h := Fin.append (fun _ : Fin E => 1) h1
    refine ⟨h,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [h,Fin.append_left,map_one]
      · simpa only [h,Fin.append_right] using hh1 j
    · intro b hb hu
      obtain ⟨x1,hx1,he1⟩ := hcover b hb hu
      let x := Fin.append (fun _ : Fin E => 1) x1
      refine ⟨x,?_,?_⟩
      · intro j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,Fin.append_left,SpecialLinearGroup.coe_one,sub_self,map_one]
          exact ⟨fun _ _ _ => rfl,trivial⟩
        · simpa only [x,Fin.append_right] using hx1 j
      · let v1 := fun j => (x1 j)⁻¹*
          ((MulAut.conj (h1 j)*PartIIProposition6_5.diagonalFieldGraph (a (j.natAdd E)) (phi (j.natAdd E)) false)^(s (j.natAdd E))) (x1 j)
        have hv : (fun j => (x j)⁻¹*
          ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=
            Fin.append (fun _ : Fin E => 1) v1 := by
          funext j
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [x,h,Fin.append_left,inv_one,map_one,mul_one]
          · simp only [x,h,Fin.append_right,v1]
        rw [hv]
        simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append,List.ofFn_const,List.prod_replicate,one_pow,one_mul] using he1
end NikolovSegal.PartIIUnitaryPrescribedUProduct
