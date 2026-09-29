/- GID: D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedMatrixOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matrix multiplication constructs endpoint-preserving edge splittings and actual overlap conjugacies. -/

import D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

open D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy

abbrev CountMat (n m : ℕ) := Matrix (Fin n) (Fin m) ℕ

/-- A numbered edge, including the identity of each parallel edge. -/
structure Edge {n m : ℕ} (M : CountMat n m) where
  source : Fin n
  target : Fin m
  number : Fin (M source target)

instance {n m : ℕ} (M : CountMat n m) : TopologicalSpace (Edge M) := ⊥
instance {n m : ℕ} (M : CountMat n m) : DiscreteTopology (Edge M) := ⟨rfl⟩

/-- The two-sided edge shift of the actual count matrix. -/
abbrev Path {n : ℕ} (M : CountMat n n) :=
  {x : ℤ → Edge M // ∀ i : ℤ, (x i).target = (x (i + 1)).source}

def shift {n : ℕ} (M : CountMat n n) (x : Path M) : Path M :=
  ⟨fun i => x.val (i + 1), fun i => x.property (i + 1)⟩

variable {n m : ℕ} (U : CountMat n m) (V : CountMat m n)

/-- All factorizations with these fixed outside endpoints. -/
abbrev Fiber (i k : Fin n) := Σ j : Fin m, Fin (U i j) × Fin (V j k)

/-- The numbered edge is ranked by the lexicographic intermediate vertex and
the two factor-edge numbers, using the proved count identity. -/
noncomputable def fiberEquiv (i k : Fin n) :
    Fin ((U * V) i k) ≃ Fiber U V i k := by
  classical
  have hcard : Fintype.card (Fiber U V i k) = (U * V) i k := by
    simp [Fiber, Matrix.mul_apply, Fintype.card_sigma, Fintype.card_prod]
  let ordered :
      Lex (Σ j : Fin m, Lex (Fin (U i j) × Fin (V j k))) ≃ Fiber U V i k :=
    ofLex.trans (Equiv.sigmaCongrRight fun _ => ofLex)
  exact (Fintype.orderIsoFinOfCardEq _ ((Fintype.card_congr ordered).trans hcard)).toEquiv
    |>.trans ordered

noncomputable def split (a : Edge (U * V)) : Edge U × Edge V :=
  let p := fiberEquiv U V a.source a.target a.number
  (⟨a.source, p.1, p.2.1⟩, ⟨p.1, a.target, p.2.2⟩)

/-- Assemble a pair while retaining its middle vertex and both edge numbers. -/
noncomputable def join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    Edge (U * V) :=
  ⟨a.source, b.target,
    (fiberEquiv U V a.source b.target).symm
      ⟨a.target, a.number, h.symm ▸ b.number⟩⟩

@[simp] theorem split_join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    split U V (join U V a b h) = (a, b) := by
  rcases a with ⟨i, j, a⟩
  rcases b with ⟨j', k, b⟩
  cases h
  let rebuild : Fiber U V i k → Edge U × Edge V := fun p =>
    (⟨i, p.1, p.2.1⟩, ⟨p.1, k, p.2.2⟩)
  have hinv := congrArg rebuild
    ((fiberEquiv U V i k).apply_symm_apply
      (⟨j, (a, b)⟩ : Fiber U V i k))
  change rebuild
      (fiberEquiv U V i k
        ((fiberEquiv U V i k).symm
          (⟨j, (a, b)⟩ : Fiber U V i k))) =
    rebuild (⟨j, (a, b)⟩ : Fiber U V i k)
  exact hinv

@[simp] theorem join_split (a : Edge (U * V)) :
    join U V (split U V a).1 (split U V a).2 (by rfl) = a := by
  rcases a with ⟨i, k, a⟩
  simp [join, split, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (fiberEquiv U V i k).symm_apply_apply a

def boundary : Boundary (Edge U) (Edge V) (Fin n) (Fin m) :=
  ⟨Edge.source, Edge.target, Edge.source, Edge.target⟩

noncomputable def toAlternating (x : Path (U * V)) : LeftPath (boundary U V) :=
  ⟨fun i => split U V (x.val i), fun i => ⟨rfl, x.property i⟩⟩

noncomputable def fromAlternating (x : LeftPath (boundary U V)) : Path (U * V) :=
  ⟨fun i => join U V (x.val i).1 (x.val i).2 (x.property i).1,
    fun i => (x.property i).2⟩

noncomputable def alternatingEquiv : Path (U * V) ≃ LeftPath (boundary U V) where
  toFun := toAlternating U V
  invFun := fromAlternating U V
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    exact join_split U V (x.val i)
  right_inv := by
    intro x
    apply Subtype.ext
    funext i
    exact split_join U V (x.val i).1 (x.val i).2 (x.property i).1

noncomputable def alternatingHomeomorph : Path (U * V) ≃ₜ LeftPath (boundary U V) where
  toEquiv := alternatingEquiv U V
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_of_discreteTopology : Continuous (split U V)).comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    let P := {p : Edge U × Edge V // p.1.target = p.2.source}
    let f : P → Edge (U * V) := fun p => join U V p.val.1 p.val.2 p.property
    have hf : Continuous f := continuous_of_discreteTopology
    have hi : Continuous (fun x : LeftPath (boundary U V) =>
        (⟨x.val i, (x.property i).1⟩ : P)) := by
      apply Continuous.subtype_mk
      exact (continuous_apply i).comp continuous_subtype_val
    exact hf.comp hi

/-- A matrix-product equality now produces a homeomorphism of its actual edge shifts. -/
noncomputable def elementaryHomeomorph : Path (U * V) ≃ₜ Path (V * U) :=
  (alternatingHomeomorph U V).trans
    ((pathHomeomorph (boundary U V)).trans (alternatingHomeomorph V U).symm)

#print axioms split_join
#print axioms join_split
#print axioms elementaryHomeomorph

end D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
