/- GID: D5/S3/QuadraticForms/ConicGDNN/Defs
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ConicGDNN/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef, mathlib/module/Mathlib.RingTheory.MvPolynomial.Homogeneous, mathlib/module/Mathlib.Analysis.Convex.Hull, mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: none
   digest: Product Lorentz cones and the two generalized doubly nonnegative cones. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Matrix MvPolynomial
open scoped BigOperators

namespace D5.S3.QuadraticForms.ConicGDNN.Defs

/-- Coordinates of the orthant and the time and spatial parts of each Lorentz block. -/
abbrev Idx (p r : ℕ) (k : Fin r → ℕ) : Type :=
  Fin p ⊕ (Σ j : Fin r, Option (Fin (k j)))

/-- The product cone of a nonnegative orthant and Lorentz cones. -/
def cone (p r : ℕ) (k : Fin r → ℕ) : Set (Idx p r k → ℝ) :=
  {y | (∀ i, 0 ≤ y (Sum.inl i)) ∧
    ∀ j, Real.sqrt (∑ i : Fin (k j), y (Sum.inr ⟨j, some i⟩) ^ 2) ≤
      y (Sum.inr ⟨j, none⟩)}

/-- Dual cone for the standard pairing. -/
def dualCone {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {u | ∀ y ∈ S, 0 ≤ u ⬝ᵥ y}

/-- Generators of extreme rays. -/
def extremeRays {ι : Type*} (S : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {s | s ∈ S ∧ s ≠ 0 ∧ ∀ a ∈ S, ∀ b ∈ S, a + b = s →
    ∃ c : ℝ, 0 ≤ c ∧ a = c • s}

/-- The Jordan square as homogeneous quadratic polynomials. -/
noncomputable def jsq {p r : ℕ} {k : Fin r → ℕ} :
    Idx p r k → MvPolynomial (Idx p r k) ℝ
  | Sum.inl i => X (Sum.inl i) ^ 2
  | Sum.inr ⟨j, none⟩ => ∑ o : Option (Fin (k j)), X (Sum.inr ⟨j, o⟩) ^ 2
  | Sum.inr ⟨j, some i⟩ => 2 * X (Sum.inr ⟨j, none⟩) * X (Sum.inr ⟨j, some i⟩)

/-- Convex hull of squares of homogeneous quadratic polynomials. -/
def sos4 (ι : Type*) : Set (MvPolynomial ι ℝ) :=
  convexHull ℝ {f | ∃ θ : MvPolynomial ι ℝ, θ.IsHomogeneous 2 ∧ f = θ ^ 2}

/-- The polynomial obtained by pairing the Jordan square with a matrix. -/
noncomputable def quartic {p r : ℕ} {k : Fin r → ℕ}
    (A : Matrix (Idx p r k) (Idx p r k) ℝ) : MvPolynomial (Idx p r k) ℝ :=
  ∑ a, ∑ b, C (A a b) * jsq a * jsq b

/-- The zeroth generalized copositive approximation. -/
def knn0 (p r : ℕ) (k : Fin r → ℕ) :
    Set (Matrix (Idx p r k) (Idx p r k) ℝ) :=
  {A | A.IsSymm ∧ quartic A ∈ sos4 _}

/-- The dual of the zeroth approximation in the symmetric matrices. -/
def dnnNN (p r : ℕ) (k : Fin r → ℕ) :
    Set (Matrix (Idx p r k) (Idx p r k) ℝ) :=
  {Xm | Xm.IsSymm ∧ ∀ A ∈ knn0 p r k, 0 ≤ (Xm * A).trace}

/-- Positive semidefinite matrices preserving the extreme rays of the dual cone. -/
def dnnBD {ι : Type*} [Fintype ι] (K : Set (ι → ℝ)) : Set (Matrix ι ι ℝ) :=
  {Xm | Xm.PosSemidef ∧ ∀ s ∈ extremeRays (dualCone K), Xm *ᵥ s ∈ K}

/-- The generalized doubly nonnegative cone inclusion. -/
def claim : Prop := ∀ (p r : ℕ) (k : Fin r → ℕ),
  (∀ j, 1 ≤ k j) → dnnNN p r k ⊆ dnnBD (cone p r k)

end D5.S3.QuadraticForms.ConicGDNN.Defs
