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

open Matrix
open private Q_mulVec Q_mul_P from
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open private pair_support_of_column_swap from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

/-- Two disconnected components can carry distinct basis labels. The resulting
rank-one positive operator has every required Bose edge marginal and fails
full Bose support. For the sole edge `{0,1}` on three qubits, this construction
with component labels `0,1` is exactly `|001⟩⟨001|`. -/
theorem disconnected_counterexample (G : SimpleGraph I) (a b : I)
    (hab : ¬ G.Reachable a b) (l m : L) (hlm : l ≠ m) :
    let w : I → L := fun i => if G.Reachable a i then l else m
    let v : (I → L) → ℂ := fun x => if x = w then 1 else 0
    let E := Matrix.vecMulVec v (star v)
    E.PosSemidef ∧
      (∀ c d (hcd : G.Adj c d), pairSymmetricProjector *
        edgeMarginal c d hcd.ne E * pairSymmetricProjector = edgeMarginal c d hcd.ne E) ∧
      P I L * E * P I L ≠ E := by
  classical
  let w : I → L := fun i => if G.Reachable a i then l else m
  let v : (I → L) → ℂ := fun x => if x = w then 1 else 0
  let E := Matrix.vecMulVec v (star v)
  have hp : E.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  refine ⟨hp,?_,?_⟩
  · intro c d hcd
    have hcol : w c = w d := by
      have hr : G.Reachable a c ↔ G.Reachable a d :=
        ⟨fun h => h.trans hcd.reachable, fun h => h.trans hcd.symm.reachable⟩
      simp only [w,hr]
    have hw : w ∘ Equiv.swap c d = w := by
      funext i
      by_cases hc : i = c
      · subst i
        simpa only [Function.comp_apply,Equiv.swap_apply_left] using hcol.symm
      by_cases hd : i = d
      · subst i
        simpa only [Function.comp_apply,Equiv.swap_apply_right] using hcol
      · simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hc hd]
    have hx (x : I → L) : x ∘ Equiv.swap c d = w ↔ x = w := by
      constructor
      · intro h
        funext i
        have hh := congrFun h (Equiv.swap c d i)
        simpa only [Function.comp_apply,Equiv.swap_apply_self,
          Equiv.apply_swap_eq_self hcol i] using hh
      · rintro rfl
        exact hw
    apply pair_support_of_column_swap c d hcd.ne E hp
    intro x y
    simp only [E,Matrix.vecMulVec_apply,v,hx]
  · intro hs
    have he : Q (Equiv.swap a b) * E = E := by
      calc
        _ = Q (Equiv.swap a b) * (P I L * E * P I L) := by rw [hs]
        _ = P I L * E * P I L := by
          rw [← Matrix.mul_assoc,← Matrix.mul_assoc,Q_mul_P]
        _ = E := hs
    have hneq : w ∘ Equiv.swap a b ≠ w := by
      intro hh
      have hv := congrFun hh a
      change w (Equiv.swap a b a) = w a at hv
      rw [Equiv.swap_apply_left] at hv
      have hwa : w a = l := if_pos (.refl a)
      have hwb : w b = m := if_neg hab
      rw [hwa,hwb] at hv
      exact hlm hv.symm
    have hx : E (w ∘ Equiv.swap a b) w = E w w :=
      (congrFun (Q_mulVec (Equiv.swap a b) (fun z => E z w)) w).symm.trans
        (congrArg (fun A => A w w) he)
    have hz : (0 : ℂ) = 1 := by
      simpa [E,Matrix.vecMulVec_apply,v,hneq] using hx
    exact zero_ne_one hz

#print axioms disconnected_counterexample

end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseComponentProjector
