/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIAmbientUnipotentDecomposition
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-! Actual untwisted large-field Part II Proposition6.2, p255.
The full U product consumes U=U1 V, not a whole-block coverage premise. -/
namespace NikolovSegal.PartIIAmbientUnipotentProduct
open Matrix PartIIUnitriangularLayers PartIICentralLevi
open PartIIAmbientUnipotentDecomposition PartIIRadicalCoordinates
universe u
/-- N and the FIELD cutoff are independent of rank and prescribed tuples.
The ONE actual determinant-one inner correction precedes ALL full U targets.
The witnesses remain genuine U and keep the ORIGINAL divisor powers. -/
theorem actual_uniform_inner_ambient_U_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ k : ℕ,
      ∀ (a : Fin N → Fin (k+4) → Fˣ) (phi : Fin N → RingAut F)
        (eps : Fin N → Bool) (d : Fin N → ℕ), (∀ i, 0<d i ∧ d i ∣ q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (k+4)) F,
        ∀ b : SpecialLinearGroup (Fin (k+4)) F, LayerDepth 1 (b.val-1) →
          ∃ x : Fin N → SpecialLinearGroup (Fin (k+4)) F,
            (∀ i, LayerDepth 1 ((x i).val-1)) ∧
            NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
              ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=b := by
  obtain ⟨N0,C0,hN0,hcentral⟩ := PartIICentralLeviProduct.actual_uniform_inner_central_levi_product q hq
  obtain ⟨N1,C1,hN1,hradical⟩ := PartIIProposition6_7.actual_proposition6_7_uniform_inner_V_product q hq
  refine ⟨N0+N1,max C0 C1,by omega,?_⟩
  intro F _ _ _ hF k a phi eps d hd
  have hF0 : C0<Fintype.card F := lt_of_le_of_lt (le_max_left _ _) hF
  have hF1 : C1<Fintype.card F := lt_of_le_of_lt (le_max_right _ _) hF
  obtain ⟨h0,hU⟩ := hcentral F hF0 (k+2)
    (fun i => a (i.castAdd N1)) (fun i => phi (i.castAdd N1))
    (fun i => eps (i.castAdd N1)) (fun i => d (i.castAdd N1)) (fun i => hd _)
  obtain ⟨h1,hh1,hV⟩ := hradical F hF1 k
    (fun i => a (i.natAdd N0)) (fun i => phi (i.natAdd N0))
    (fun i => eps (i.natAdd N0)) (fun i => d (i.natAdd N0)) (fun i => hd _)
  let h := Fin.append h0 h1
  refine ⟨h,?_⟩
  intro b hb
  obtain ⟨g,v,hg,hv,hgv⟩ := actual_ambient_U_decomposition (n:=k+2) b hb
  obtain ⟨x0,hx0,hp0⟩ := hU g hg
  obtain ⟨x1,hx1,hp1⟩ := hV v hv
  let x := Fin.append (fun i => embed (x0 i)) x1
  have hx : ∀ i, LayerDepth 1 ((x i).val-1) := by
    simp only [x,Fin.forall_fin_add,Fin.append_left,Fin.append_right]
    exact ⟨fun i => actual_central_embed_unitriangular (x0 i) (hx0 i),fun i => (hx1 i).1⟩
  let v0 := fun i => (embed (x0 i))⁻¹*
    ((MulAut.conj (h0 i)*PartIIProposition6_5.diagonalFieldGraph (a (i.castAdd N1))
      (phi (i.castAdd N1)) (eps (i.castAdd N1)))^(d (i.castAdd N1))) (embed (x0 i))
  let v1 := fun i => (x1 i)⁻¹*
    ((MulAut.conj (h1 i)*PartIIProposition6_5.diagonalFieldGraph (a (i.natAdd N0))
      (phi (i.natAdd N0)) (eps (i.natAdd N0)))^(d (i.natAdd N0))) (x1 i)
  have hvalues : (fun i => (x i)⁻¹*
      ((MulAut.conj (h i)*PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i))^(d i)) (x i))=
      Fin.append v0 v1 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [x,h,v0,Fin.append_left]
    · simp only [x,h,v1,Fin.append_right]
  refine ⟨x,hx,?_⟩
  rw [hvalues]
  change (List.ofFn (Fin.append v0 v1)).prod=b
  rw [List.ofFn_fin_append,List.prod_append]
  exact (congrArg₂ (·*·) hp0 hp1).trans hgv
end NikolovSegal.PartIIAmbientUnipotentProduct
