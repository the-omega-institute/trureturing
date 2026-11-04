/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tensor factorization of the graph component Bose projector. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

/-! The actual component permutation average and its tensor factorization. -/

open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseComponentProjector

set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

attribute [local instance] Classical.propDecidable

private noncomputable instance componentFintype (G : SimpleGraph I) :
    Fintype G.ConnectedComponent := Fintype.ofFinite _

private noncomputable def assemble (G : SimpleGraph I)
    (τ : ∀ C : G.ConnectedComponent, Equiv.Perm C.supp) : Equiv.Perm I :=
  ((Equiv.sigmaFiberEquiv G.connectedComponentMk).symm.trans
    (Equiv.sigmaCongrRight τ)).trans (Equiv.sigmaFiberEquiv G.connectedComponentMk)

omit [Fintype I] [DecidableEq I] in
private lemma assemble_apply (G : SimpleGraph I)
    (τ : ∀ C : G.ConnectedComponent, Equiv.Perm C.supp)
    (C : G.ConnectedComponent) (i : C.supp) :
    assemble G τ i.val = (τ C i).val := by
  rcases i with ⟨i, hi⟩
  change G.connectedComponentMk i = C at hi
  subst C
  rfl

private noncomputable def componentPermEquiv (G : SimpleGraph I) :
    componentGroup G ≃ (∀ C : G.ConnectedComponent, Equiv.Perm C.supp) where
  toFun σ C := σ.val.subtypeEquiv (fun i => by
    change G.connectedComponentMk i = C ↔ G.connectedComponentMk (σ.val i) = C
    rw [← SimpleGraph.ConnectedComponent.sound (σ.property i)])
  invFun τ := ⟨assemble G τ, fun i =>
    SimpleGraph.ConnectedComponent.exact
      ((τ (G.connectedComponentMk i) ⟨i,rfl⟩).property.symm)⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rfl
  right_inv τ := by
    funext C
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact assemble_apply G τ C i

open private Q_apply Average.expect_formula from
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

omit [Fintype L] in
private lemma assemble_Q (G : SimpleGraph I)
    (τ : ∀ C : G.ConnectedComponent, Equiv.Perm C.supp) (x y : I → L) :
    Q (assemble G τ) x y =
      ∏ C : G.ConnectedComponent, Q (τ C) (fun i => x i.val) (fun i => y i.val) := by
  simp only [Q_apply]
  have he : y = x ∘ assemble G τ ↔
      ∀ C : G.ConnectedComponent, (fun i : C.supp => y i.val) =
        (fun i : C.supp => x i.val) ∘ τ C := by
    constructor
    · intro h C
      funext i
      simpa only [Function.comp_apply, assemble_apply G τ C i] using congrFun h i.val
    · intro h
      funext i
      exact congrFun (h (G.connectedComponentMk i)) ⟨i,rfl⟩
  simp only [he]
  by_cases h : ∀ C : G.ConnectedComponent, (fun i : C.supp => y i.val) =
      (fun i : C.supp => x i.val) ∘ τ C
  · simp [h]
  · rw [if_neg h]
    obtain ⟨C, hC⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ C)
    exact if_neg hC

/-- The tensor product of the symmetric projectors of all connected components,
expressed in the original tensor basis. Singleton components remain as identity factors. -/
noncomputable def tensorProjector (G : SimpleGraph I) :
    Matrix (I → L) (I → L) ℂ :=
  fun x y => ∏ C : G.ConnectedComponent,
    P C.supp L (fun i => x i.val) (fun i => y i.val)

/-- The permutation average is exactly the tensor product over all components,
with no connectedness or nonemptiness assumption on the graph. -/
theorem factorization (G : SimpleGraph I) :
    componentProjector (L := L) G = tensorProjector G := by
  have hcard : Fintype.card (componentGroup G) =
      ∏ C : G.ConnectedComponent, Fintype.card (Equiv.Perm C.supp) := by
    rw [Fintype.card_congr (componentPermEquiv G), Fintype.card_pi]
  ext x y
  have hsum : (∑ σ : componentGroup G, Q σ.val x y) =
      ∏ C : G.ConnectedComponent, ∑ τ : Equiv.Perm C.supp,
        Q τ (fun i => x i.val) (fun i => y i.val) := by
    rw [← (componentPermEquiv G).symm.sum_comp]
    change (∑ τ : ∀ C : G.ConnectedComponent, Equiv.Perm C.supp,
      Q (assemble G τ) x y) = _
    simp_rw [assemble_Q]
    exact (Fintype.prod_sum (fun (C : G.ConnectedComponent) (τ : Equiv.Perm C.supp) =>
      Q τ (fun i => x i.val) (fun i => y i.val))).symm
  simp only [componentProjector, tensorProjector, P, Average.expect_formula,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  change (Fintype.card (componentGroup G) : ℂ)⁻¹ *
    (∑ σ : componentGroup G, Q σ.val x y) = _
  rw [hsum, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hcard, Nat.cast_prod]

#print axioms factorization

end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseComponentProjector
