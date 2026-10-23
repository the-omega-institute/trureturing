/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryAmbientOddUProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryAmbientOddUProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryOddCentralUProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII printed p255 Case2: actual odd U*=U1*V* for arbitrary genuine
prescribed diagonal-similitude/field tuples. ONE global SU correction
precedes every actual U target; ordered factors are never commuted. -/
open Lean Elab Term in
elab "unitaryAmbientEven%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitaryAmbientEvenUProduct"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) => n.toString.endsWith suffix && match env.getModuleIdxFor? n with
    | none => false
    | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryAmbientEvenUProduct"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Accepted actual ambient even U kernel {id} not found"
namespace NikolovSegal.PartIIUnitaryAmbientOddUProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open PartIIUnitaryOddCentralUProduct PartIIRadicalCoordinates UnitaryField
universe u
/-- Entire actual positive U in all odd ranks 2(d+2)+3, arbitrary genuine
prescribed D/Phi tuples. Both decompositions and all three suppliers are
proved inputs; no coverage, lift or action/power identity is assumed. -/
theorem actual_uniform_ambient_odd_U_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ d : ℕ, ∀ (a : Fin N → Fin (2*(d+2)+1+2) → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ), (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (2*(d+2)+1+2)) F,
        (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin (2*(d+2)+1+2)) F,
          LayerDepth 1 (b.val-1) → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (2*(d+2)+1+2)) F,
            (∀ j, LayerDepth 1 ((x j).val-1) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=b := by
  classical
  obtain ⟨L,CL,hL,hcentral⟩ := actual_uniform_central_odd_U_prescribed_product q hq
  obtain ⟨V,CV,hV,hradical⟩ := (unitaryAmbientEven% radical_with_middle_rank) q hq
  refine ⟨L+V,max CL CV,by omega,?_⟩
  intro F _ _ _ hF ι hinv hne d a c ha phi s hs
  obtain ⟨h0,hh0,hcover0⟩ := hcentral F ((le_max_left _ _).trans_lt hF) ι hinv hne (d+2)
    (fun j => a (j.castAdd V)) (fun j => c (j.castAdd V)) (fun j => ha _)
    (fun j => phi (j.castAdd V)) (fun j => s (j.castAdd V)) (fun j => hs _)
  obtain ⟨h1,hd1,hh1,hcover1⟩ := hradical F ((le_max_right _ _).trans_lt hF) ι hinv hne
    (2*(d+2)+1) (by omega) (fun j => a (j.natAdd L)) (fun j => c (j.natAdd L))
    (fun j => ha _) (fun j => phi (j.natAdd L)) (fun j => s (j.natAdd L)) (fun j => hs _)
  let h := Fin.append h0 h1
  refine ⟨h,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [h,Fin.append_left] using hh0 j
    · simpa only [h,Fin.append_right] using hh1 j
  · intro b hb hbu
    obtain ⟨g,v,hg,hgu,hv,hvu,hgv⟩ := PartIIUnitaryLeviDecomposition.actual_unitary_ambient_U_decomposition ι b hb hbu
    obtain ⟨z0,hz0,he0⟩ := hcover0 g hg hgu
    obtain ⟨x1,hx1,he1⟩ := hcover1 v hv hvu
    let x0 := fun j => PartIICentralLevi.embed (z0 j)
    let x := Fin.append x0 x1
    refine ⟨x,?_,?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [x,Fin.append_left,x0] using
          ⟨PartIIAmbientUnipotentDecomposition.actual_central_embed_unitriangular _ (hz0 j).1,
            by rw [PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi,(hz0 j).2]⟩
      · simpa only [x,Fin.append_right] using ⟨(hx1 j).1.1,(hx1 j).2⟩
    · let v0 := fun j => (x0 j)⁻¹*
        ((MulAut.conj (h0 j)*PartIIProposition6_5.diagonalFieldGraph (a (j.castAdd V)) (phi (j.castAdd V)) false)^(s (j.castAdd V))) (x0 j)
      let v1 := fun j => (x1 j)⁻¹*
        ((MulAut.conj (h1 j)*PartIIProposition6_5.diagonalFieldGraph (a (j.natAdd L)) (phi (j.natAdd L)) false)^(s (j.natAdd L))) (x1 j)
      have he : orderedProduct v0*orderedProduct v1=b := by
        rw [show orderedProduct v0=PartIICentralLevi.embed g from he0,
          show orderedProduct v1=v from he1]
        exact hgv
      have hvalues : (fun j => (x j)⁻¹*
        ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=Fin.append v0 v1 := by
        funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [x,h,Fin.append_left,v0]
        · simp only [x,h,Fin.append_right,v1]
      rw [hvalues]
      simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append] using he
end NikolovSegal.PartIIUnitaryAmbientOddUProduct
