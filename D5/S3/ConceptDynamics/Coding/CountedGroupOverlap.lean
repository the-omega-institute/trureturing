/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupOverlap
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Group-ring coefficients construct labelled edge splittings and equivariant one-step overlap conjugacies. -/

import D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

open D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
open D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding

universe u
variable {H : Type u} [Group H] [Fintype H]

abbrev GroupMat (H : Type u) [Group H] (n m : ℕ) :=
  Matrix (Fin n) (Fin m) (MonoidAlgebra ℕ H)

/-- Parallel edges retain both their group label and their number within that label. -/
structure Edge {n m : ℕ} (M : GroupMat H n m) where
  source : Fin n
  target : Fin m
  label : H
  number : Fin ((M source target).coeff label)

instance {n m : ℕ} (M : GroupMat H n m) : TopologicalSpace (Edge M) := ⊥
instance {n m : ℕ} (M : GroupMat H n m) : DiscreteTopology (Edge M) := ⟨rfl⟩

abbrev Path {n : ℕ} (M : GroupMat H n n) :=
  {x : ℤ → Edge M // ∀ i : ℤ, (x i).target = (x (i + 1)).source}

def shift {n : ℕ} (M : GroupMat H n n) (x : Path M) : Path M :=
  ⟨fun i => x.val (i + 1), fun i => x.property (i + 1)⟩

/-- The time step includes the ordered multiplication of the current edge label. -/
def step {n : ℕ} (M : GroupMat H n n) (p : Path M × H) : Path M × H :=
  (shift M p.1, p.2 * (p.1.val 0).label)

variable {n m : ℕ} (U : GroupMat H n m) (V : GroupMat H m n)

abbrev Fiber (i k : Fin n) (g : H) :=
  Σ j : Fin m, Σ h : H,
    Fin ((U i j).coeff h) × Fin ((V j k).coeff (h⁻¹ * g))

noncomputable def fiberEquiv (i k : Fin n) (g : H) :
    Fin (((U * V) i k).coeff g) ≃ Fiber U V i k g := by
  classical
  have coeff_product_finite (a b : MonoidAlgebra ℕ H) :
      (a * b).coeff g = ∑ h : H, a.coeff h * b.coeff (h⁻¹ * g) := by
    rw [MonoidAlgebra.coeff_mul_apply_left]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
  have hcard : Fintype.card (Fiber U V i k g) = ((U * V) i k).coeff g := by
    simp [Fiber, Matrix.mul_apply, Fintype.card_sigma, Fintype.card_prod,
      coeff_product_finite]
  exact (Fintype.equivFinOfCardEq hcard).symm

noncomputable def split (a : Edge (U * V)) : Edge U × Edge V :=
  let totalFiberEquiv :
      (Σ g : H, Fin (((U * V) a.source a.target).coeff g)) ≃
        (Σ g : H, Fiber U V a.source a.target g) :=
    Equiv.sigmaCongrRight fun g => fiberEquiv U V a.source a.target g
  let p := totalFiberEquiv ⟨a.label, a.number⟩
  (⟨a.source, p.2.1, p.2.2.1, p.2.2.2.1⟩,
   ⟨p.2.1, a.target, p.2.2.1⁻¹ * p.1, p.2.2.2.2⟩)

noncomputable def join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    Edge (U * V) :=
  let totalFiberEquiv :
      (Σ g : H, Fin (((U * V) a.source b.target).coeff g)) ≃
        (Σ g : H, Fiber U V a.source b.target g) :=
    Equiv.sigmaCongrRight fun g => fiberEquiv U V a.source b.target g
  let p := totalFiberEquiv.symm
    ⟨a.label * b.label,
      a.target, a.label, a.number, by simpa using h.symm ▸ b.number⟩
  ⟨a.source, b.target, p.1, p.2⟩

@[simp] theorem split_join (a : Edge U) (b : Edge V) (h : a.target = b.source) :
    split U V (join U V a b h) = (a, b) := by
  rcases a with ⟨i, j, g, a⟩
  rcases b with ⟨j', k, h', b⟩
  cases h
  let totalFiberEquiv :
      (Σ h : H, Fin (((U * V) i k).coeff h)) ≃ (Σ h : H, Fiber U V i k h) :=
    Equiv.sigmaCongrRight fun h => fiberEquiv U V i k h
  let p : Σ h : H, Fiber U V i k h :=
    ⟨g * h', j, g, a, by simpa using b⟩
  let rebuild : (Σ h : H, Fiber U V i k h) → Edge U × Edge V := fun q =>
    (⟨i, q.2.1, q.2.2.1, q.2.2.2.1⟩,
     ⟨q.2.1, k, q.2.2.1⁻¹ * q.1, q.2.2.2.2⟩)
  change rebuild (totalFiberEquiv (totalFiberEquiv.symm p)) =
    (⟨i, j, g, a⟩, ⟨j, k, h', b⟩)
  rw [Equiv.apply_symm_apply]
  simp [rebuild, p]

@[simp] theorem join_split (a : Edge (U * V)) :
    join U V (split U V a).1 (split U V a).2 (by rfl) = a := by
  rcases a with ⟨i, k, g, a⟩
  let totalFiberEquiv :
      (Σ h : H, Fin (((U * V) i k).coeff h)) ≃ (Σ h : H, Fiber U V i k h) :=
    Equiv.sigmaCongrRight fun h => fiberEquiv U V i k h
  let rebuild : (Σ h : H, Fin (((U * V) i k).coeff h)) → Edge (U * V) :=
    fun q => ⟨i, k, q.1, q.2⟩
  let q : Σ h : H, Fiber U V i k h := totalFiberEquiv ⟨g, a⟩
  let recovered : Σ h : H, Fiber U V i k h :=
    ⟨q.2.2.1 * (q.2.2.1⁻¹ * q.1), q.2.1, q.2.2.1, q.2.2.2.1,
      by simpa [mul_assoc] using q.2.2.2.2⟩
  have recovered_eq : recovered = q := by
    rcases q with ⟨qg, qj, qh, qa, qb⟩
    apply Sigma.ext
    · simp [recovered, mul_assoc]
    · apply HEq.of_eq
      apply Sigma.ext
      · rfl
      · apply HEq.of_eq
        apply Sigma.ext
        · rfl
        · apply HEq.of_eq
          apply Prod.ext
          · rfl
          · apply Fin.ext
            rfl
  have hinv := congrArg rebuild
    (totalFiberEquiv.symm_apply_apply
      (⟨g, a⟩ : Σ h : H, Fin (((U * V) i k).coeff h)))
  simp only [join, split]
  change rebuild (totalFiberEquiv.symm recovered) = rebuild ⟨g, a⟩
  rw [recovered_eq]
  simpa [q] using hinv

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

noncomputable def unpack (p : Path (U * V) × H) : LeftPath (boundary U V) × H :=
  (toAlternating U V p.1, p.2)

noncomputable def repack (p : LeftPath (boundary U V) × H) : Path (U * V) × H :=
  (fromAlternating U V p.1, p.2)

section Topology
variable [TopologicalSpace H] [IsTopologicalGroup H]

/-- A homeomorphism together with the specified time and group laws. -/
structure GroupConjugacy {a b : ℕ} (A : GroupMat H a a) (B : GroupMat H b b) where
  homeomorph : Path A × H ≃ₜ Path B × H
  time_law : ∀ p, homeomorph (step A p) = step B (homeomorph p)
  group_law : ∀ g p, homeomorph (translate g p) = translate g (homeomorph p)

end Topology

#print axioms split_join
#print axioms join_split

end D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
