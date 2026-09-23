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
import Mathlib.Data.Fintype.BigOperators

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

theorem fiber_card (i k : Fin n) :
    Fintype.card (Fiber U V i k) = (U * V) i k := by
  simp [Fiber, Matrix.mul_apply, Fintype.card_sigma, Fintype.card_prod]

/-- The equivalence is constructed from the proved count identity, not supplied as a premise. -/
noncomputable def fiberEquiv (i k : Fin n) :
    Fin ((U * V) i k) ≃ Fiber U V i k :=
  (Fintype.equivFinOfCardEq (fiber_card U V i k)).symm

noncomputable def split (a : Edge (U * V)) : Edge U × Edge V :=
  let p := fiberEquiv U V a.source a.target a.number
  (⟨a.source, p.1, p.2.1⟩, ⟨p.1, a.target, p.2.2⟩)

@[simp] theorem split_source (a : Edge (U * V)) :
    (split U V a).1.source = a.source := rfl

@[simp] theorem split_target (a : Edge (U * V)) :
    (split U V a).2.target = a.target := rfl

@[simp] theorem split_boundary (a : Edge (U * V)) :
    (split U V a).1.target = (split U V a).2.source := rfl

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
  dsimp at h
  subst j'
  simp [join, split, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

@[simp] theorem join_split (a : Edge (U * V)) :
    join U V (split U V a).1 (split U V a).2 (split_boundary U V a) = a := by
  rcases a with ⟨i, k, a⟩
  simp [join, split, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (fiberEquiv U V i k).symm_apply_apply a

/-- Edge counts are not replaced by the support relation. -/
theorem split_injective : Function.Injective (split U V) := by
  intro a b h
  have hs := congrArg (fun p : Edge U × Edge V => p.1) h
  have ht := congrArg (fun p : Edge U × Edge V => p.2) h
  calc
    a = join U V (split U V a).1 (split U V a).2 (split_boundary U V a) :=
      (join_split U V a).symm
    _ = join U V (split U V b).1 (split U V b).2 (split_boundary U V b) := by
      simp only [hs, ht]
    _ = b := join_split U V b

def boundary : Boundary (Edge U) (Edge V) (Fin n) (Fin m) :=
  ⟨Edge.source, Edge.target, Edge.source, Edge.target⟩

noncomputable def toAlternating (x : Path (U * V)) : LeftPath (boundary U V) :=
  ⟨fun i => split U V (x.val i), fun i => ⟨rfl, x.property i⟩⟩

noncomputable def fromAlternating (x : LeftPath (boundary U V)) : Path (U * V) :=
  ⟨fun i => join U V (x.val i).1 (x.val i).2 (x.property i).1,
    fun i => (x.property i).2⟩

@[simp] theorem from_to (x : Path (U * V)) :
    fromAlternating U V (toAlternating U V x) = x := by
  apply Subtype.ext
  funext i
  exact join_split U V (x.val i)

@[simp] theorem to_from (x : LeftPath (boundary U V)) :
    toAlternating U V (fromAlternating U V x) = x := by
  apply Subtype.ext
  funext i
  exact split_join U V (x.val i).1 (x.val i).2 (x.property i).1

noncomputable def alternatingEquiv : Path (U * V) ≃ LeftPath (boundary U V) where
  toFun := toAlternating U V
  invFun := fromAlternating U V
  left_inv := from_to U V
  right_inv := to_from U V

@[simp] theorem toAlternating_shift (x : Path (U * V)) :
    toAlternating U V (shift (U * V) x) = leftShift (boundary U V) (toAlternating U V x) := rfl

@[simp] theorem fromAlternating_shift (x : LeftPath (boundary U V)) :
    fromAlternating U V (leftShift (boundary U V) x) =
      shift (U * V) (fromAlternating U V x) := rfl

theorem continuous_toAlternating : Continuous (toAlternating U V) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous (split U V)).comp
    ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_fromAlternating : Continuous (fromAlternating U V) := by
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

noncomputable def alternatingHomeomorph : Path (U * V) ≃ₜ LeftPath (boundary U V) where
  toEquiv := alternatingEquiv U V
  continuous_toFun := continuous_toAlternating U V
  continuous_invFun := continuous_fromAlternating U V

/-- A matrix-product equality now produces a homeomorphism of its actual edge shifts. -/
noncomputable def elementaryHomeomorph : Path (U * V) ≃ₜ Path (V * U) :=
  (alternatingHomeomorph U V).trans
    ((pathHomeomorph (boundary U V)).trans (alternatingHomeomorph V U).symm)

theorem elementary_apply (x : Path (U * V)) :
    elementaryHomeomorph U V x =
      fromAlternating V U (forward (boundary U V) (toAlternating U V x)) := rfl

theorem elementary_symm_apply (x : Path (V * U)) :
    (elementaryHomeomorph U V).symm x =
      fromAlternating U V (backward (boundary U V) (toAlternating V U x)) := rfl

theorem elementary_shift (x : Path (U * V)) :
    elementaryHomeomorph U V (shift (U * V) x) =
      shift (V * U) (elementaryHomeomorph U V x) := by
  apply Subtype.ext
  rfl

theorem elementary_inverse_shift (x : Path (V * U)) :
    (elementaryHomeomorph U V).symm (shift (V * U) x) =
      shift (U * V) ((elementaryHomeomorph U V).symm x) := by
  apply (elementaryHomeomorph U V).injective
  rw [(elementaryHomeomorph U V).apply_symm_apply,
    elementary_shift, (elementaryHomeomorph U V).apply_symm_apply]

private theorem join_congr (a a' : Edge U) (b b' : Edge V)
    (h : a.target = b.source) (h' : a'.target = b'.source)
    (ha : a = a') (hb : b = b') : join U V a b h = join U V a' b' h' := by
  subst a'
  subst b'
  rfl

theorem elementary_window (x y : Path (U * V)) (i : ℤ)
    (h0 : x.val i = y.val i) (h1 : x.val (i + 1) = y.val (i + 1)) :
    (elementaryHomeomorph U V x).val i = (elementaryHomeomorph U V y).val i := by
  exact join_congr V U _ _ _ _
    ((forward (boundary U V) (toAlternating U V x)).property i).1
    ((forward (boundary U V) (toAlternating U V y)).property i).1
    (congrArg (fun a => (split U V a).2) h0)
    (congrArg (fun a => (split U V a).1) h1)

theorem elementary_inverse_window (x y : Path (V * U)) (i : ℤ)
    (hm : x.val (i - 1) = y.val (i - 1)) (h0 : x.val i = y.val i) :
    ((elementaryHomeomorph U V).symm x).val i =
      ((elementaryHomeomorph U V).symm y).val i := by
  exact join_congr U V _ _ _ _
    ((backward (boundary U V) (toAlternating V U x)).property i).1
    ((backward (boundary U V) (toAlternating V U y)).property i).1
    (congrArg (fun a => (split V U a).2) hm)
    (congrArg (fun a => (split V U a).1) h0)

/-- A concrete two-factor fiber has two distinct elements despite identical outer endpoints. -/
theorem parallel_factor_identity :
    (⟨0, (0, 0)⟩ : Fiber (fun _ : Fin 1 => fun _ : Fin 1 => 2)
      (fun _ : Fin 1 => fun _ : Fin 1 => 1) 0 0) ≠ ⟨0, (1, 0)⟩ := by
  decide

#print axioms fiber_card
#print axioms split_join
#print axioms join_split
#print axioms elementaryHomeomorph
#print axioms elementary_shift
#print axioms elementary_window
#print axioms elementary_inverse_window

end D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
