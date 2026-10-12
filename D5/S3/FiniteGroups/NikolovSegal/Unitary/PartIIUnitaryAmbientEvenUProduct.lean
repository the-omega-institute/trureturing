/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryAmbientEvenUProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryAmbientEvenUProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalPrescribedProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryCentralEvenProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII printed p255 Case2: consume the ACTUAL central even U1
supplier, newly proved prescribed V* supplier and unchanged genuine
U*=U1*V* decomposition. ONE correction tuple precedes every full
positive-unitary target. Tuple scope is the genuine manufactured
paired diagonal/field actions; bare/full-SU coverage is not asserted. -/
open Lean Elab Term in
elab "unitaryTypeAProduct%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryTypeALeviProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) => n.toString.endsWith suffix && match env.getModuleIdxFor? n with
    | none => false
    | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTypeALeviProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Actual unitary type-A product kernel {id} not found"
namespace NikolovSegal.PartIIUnitaryAmbientEvenUProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open PartIIUnitaryTypeALeviProduct PartIIUnitaryCentralEvenProduct
open PartIIUnitaryRadicalPrescribedProduct PartIIRadicalCoordinates
universe u
private theorem gamma_eq {F : Type u} [Field F] (ι : RingAut F) {d : ℕ}
    (a : Fin d → Fˣ) (phi : RingAut F) :
    PartIIProposition6_5.diagonalFieldGraph ((unitaryTypeAProduct% ambientWeights) ι a) phi false=
      diagonalField ι a phi := by
  apply MulEquiv.ext
  intro g
  rfl

private theorem radical_with_middle_rank (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ n : ℕ, 4≤n → ∀ (a : Fin N → Fin (n+2) → Fˣ) (c : Fin N → (UnitaryField.fixedField ι)ˣ),
      (∀ i j, ι (a i j:F)*(a i j.rev:F)=((c i:UnitaryField.fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ),
      (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (n+2)) F,
        (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin (n+2)) F, InRadical b → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (n+2)) F,
            (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=b := by
  obtain ⟨N,C,hN,hcover⟩ := actual_uniform_unitary_radical_prescribed_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
  exact hcover F hF ι hinv hne k

/-- ALL actual positive unitary targets in every even ambient rank
2(d+2)+2. Chosen length/cutoff precede every field/rank/tuple, ONE
actual unitary inner correction precedes ALL targets, and actual
positive unitary witnesses give the ordered exact-length VALUES.
No central/radical/decomposition/coverage premise is retained. -/
theorem actual_uniform_ambient_even_U_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin (d+2) → Fˣ) (phi : Fin N → RingAut F)
        (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*(d+2)+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin (2*(d+2)+2)) F,
          LayerDepth 1 (b.val-1) → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*(d+2)+2)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (x j))=b := by
  classical
  obtain ⟨L,CL,hL,hcentral⟩ := actual_uniform_central_even_U_product q hq
  obtain ⟨V,CV,hV,hradical⟩ := radical_with_middle_rank q hq
  refine ⟨L+V,max CL CV,by omega,?_⟩
  intro F _ _ _ hF ι hinv hne d a phi s hs
  obtain ⟨h0,hh0,hcover0⟩ := hcentral F ((le_max_left _ _).trans_lt hF) ι hinv hne (d+2)
    (fun j => a (j.castAdd V)) (fun j => phi (j.castAdd V))
    (fun j => s (j.castAdd V)) (fun j => hs _)
  let w := fun j : Fin V => (unitaryTypeAProduct% ambientWeights) ι (a (j.natAdd L))
  have hw : ∀ j i, ι (w j i:F)*(w j i.rev:F)=((1:(UnitaryField.fixedField ι)ˣ):UnitaryField.fixedField ι) := by
    intro j i
    exact (unitaryCentral% extend_unitary) ι hinv _
      ((unitaryTypeA% pairedUnits_unitary) ι hinv (a (j.natAdd L))) 1 i
  have hradicalEven := hradical F ((le_max_right _ _).trans_lt hF) ι hinv hne (2*(d+2)) (by omega)
  obtain ⟨h1,hd1,hh1,hcover1⟩ := hradicalEven w (fun _ => 1) hw (fun j => phi (j.natAdd L))
    (fun j => s (j.natAdd L)) (fun j => hs _)
  let h := Fin.append h0 h1
  refine ⟨h,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [h,Fin.append_left] using hh0 j
    · simpa only [h,Fin.append_right] using hh1 j
  · intro b hb hbu
    obtain ⟨g,v,hg,hgu,hv,hvu,hgv⟩ := PartIIUnitaryLeviDecomposition.actual_unitary_ambient_U_decomposition ι b hb hbu
    obtain ⟨x0,hx0,he0⟩ := hcover0 g hg hgu
    obtain ⟨x1,hx1,he1⟩ := hcover1 v hv hvu
    have he1' : orderedProduct (fun j => (x1 j)⁻¹*
        ((MulAut.conj (h1 j)*diagonalField ι (a (j.natAdd L)) (phi (j.natAdd L)))^(s (j.natAdd L))) (x1 j))=v := by
      simpa only [w,gamma_eq] using he1
    let x := Fin.append x0 x1
    refine ⟨x,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [x,Fin.append_left] using hx0 j
      · simpa only [x,Fin.append_right] using ⟨(hx1 j).1.1,(hx1 j).2⟩
    · let v0 := fun j => (x0 j)⁻¹*((MulAut.conj (h0 j)*diagonalField ι (a (j.castAdd V)) (phi (j.castAdd V)))^(s (j.castAdd V))) (x0 j)
      let v1 := fun j => (x1 j)⁻¹*((MulAut.conj (h1 j)*diagonalField ι (a (j.natAdd L)) (phi (j.natAdd L)))^(s (j.natAdd L))) (x1 j)
      have he : orderedProduct v0*orderedProduct v1=b := by
        rw [show orderedProduct v0=PartIICentralLevi.embed g from he0,
          show orderedProduct v1=v from he1']
        exact hgv
      have hvalues : (fun j => (x j)⁻¹*((MulAut.conj (h j)*diagonalField ι (a j) (phi j))^(s j)) (x j))=
          Fin.append v0 v1 := by
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,h,Fin.append_left,v0]
        · simp only [x,h,Fin.append_right,v1]
      rw [hvalues]
      simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append] using he
end NikolovSegal.PartIIUnitaryAmbientEvenUProduct
