/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryCentralEvenProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryCentralEvenProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryEvenPUniform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII p255 Case2. Actual even central U1=U2 P is reconstructed by
CONSUMING the proved type-A Proposition6.5 branch and even P branch.
The TWO correction tuples are fixed before every actual U1 target.
This is the whole central EVEN U1, not the ambient V* or full SU. -/
namespace NikolovSegal.PartIIUnitaryCentralEvenProduct
open Matrix PartIIUnitriangularLayers PartIIUnitaryUpperTorus
open PartIIUnitaryTypeALeviProduct PartIIUnitaryEvenPUniform
universe u

/-- Actual uniform prescribed diagonal/field VALUE coverage of the
ENTIRE even-dimensional central positive unitary U1. Length/cutoff
precede all fields/ranks/tuples; ONE ambient unitary h precedes all
actual targets b, and every witness is positive UNITARY. -/
theorem actual_uniform_central_even_U_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin d → Fˣ) (phi : Fin N → RingAut F)
        (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin (2*d)) F,
          LayerDepth 1 (b.val-1) → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*d+2)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            NikolovSegal.orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (x j))=
              PartIICentralLevi.embed b := by
  classical
  obtain ⟨L,CL,hL,hLevi⟩ := actual_uniform_unitary_typeA_Levi_product q hq
  obtain ⟨P,CP,hP,hComplement⟩ := actual_uniform_even_P_prescribed_product q hq
  refine ⟨L+P,max CL CP,by omega,?_⟩
  intro F _ _ _ hF ι hinv hne d a phi s hs
  obtain ⟨h0,hh0,hcover0⟩ := hLevi F ((le_max_left _ _).trans_lt hF) ι hinv hne d
    (fun j => a (j.castAdd P)) (fun j => phi (j.castAdd P)) (fun j => s (j.castAdd P)) (fun j => hs _)
  obtain ⟨h1,hh1,hcover1⟩ := hComplement F ((le_max_right _ _).trans_lt hF) ι hinv hne d
    (fun j => a (j.natAdd L)) (fun j => phi (j.natAdd L)) (fun j => s (j.natAdd L)) (fun j => hs _)
  let h := Fin.append h0 h1
  refine ⟨h,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [h,Fin.append_left] using hh0 j
    · simpa only [h,Fin.append_right] using hh1 j
  · intro b hb hbu
    obtain ⟨g,B,hg,hB,hgB⟩ := PartIIUnitaryEvenP.actual_even_unitary_U_decomposition ι hinv b hb hbu
    obtain ⟨z0,hz0,he0⟩ := hcover0 g hg
    obtain ⟨z1,hz1,he1⟩ := hcover1 B hB
    let z := fun j => levi ι (z0 j)
    let x := Fin.append z z1
    refine ⟨x,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [x,Fin.append_left,z] using ⟨(hz0 j).2.1,(hz0 j).2.2⟩
      · simpa only [x,Fin.append_right] using hz1 j
    · let v0 := fun j => (z j)⁻¹*((MulAut.conj (h0 j)*diagonalField ι (a (j.castAdd P)) (phi (j.castAdd P)))^(s (j.castAdd P))) (z j)
      let v1 := fun j => (z1 j)⁻¹*((MulAut.conj (h1 j)*diagonalField ι (a (j.natAdd L)) (phi (j.natAdd L)))^(s (j.natAdd L))) (z1 j)
      have hv : (fun j => (x j)⁻¹*((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (x j))=Fin.append v0 v1 := by
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,h,Fin.append_left,v0]
        · simp only [x,h,Fin.append_right,v1]
      rw [hv]
      have he : NikolovSegal.orderedProduct v0*NikolovSegal.orderedProduct v1=
          PartIICentralLevi.embed b := by
        rw [show NikolovSegal.orderedProduct v0=levi ι g from he0,
          show NikolovSegal.orderedProduct v1=PartIICentralLevi.embed (PartIIUnitaryEvenP.p B) from he1]
        change PartIICentralLevi.embed (PartIIUnitaryTypeALevi.embed ι g)*PartIICentralLevi.embed (PartIIUnitaryEvenP.p B)=_
        rw [← map_mul,hgB]
      simpa only [NikolovSegal.orderedProduct,List.ofFn_fin_append,List.prod_append] using he
end NikolovSegal.PartIIUnitaryCentralEvenProduct
