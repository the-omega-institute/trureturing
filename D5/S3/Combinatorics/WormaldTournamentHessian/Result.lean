/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Analytic Hessian and determinant-square structure of regular tournaments. -/

/-
The utility classification is none: the objects and intended conclusion are
general theorems over arbitrary finite tournaments, not finite computations.
This is an unfinished implementation of Conjecture 6; no resolution is asserted.
Definitions have proof_shape bind-only (definition), escape_witness none.
Frozen D5 dependencies: none.
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! # The tournament determinant and its analytic Hessian -/

public section

open scoped Topology
open Matrix Filter

namespace D5.S3.Combinatorics.WormaldTournamentHessian.Result

/-- An irreflexive orientation of every pair, with constant out-degree. -/
def IsRegularTournament {d : ℕ} (A : Fin d → Fin d → Bool) : Prop :=
  (∀ i, A i i = false) ∧
  (∀ i j, i ≠ j → (A i j = true ↔ A j i = false)) ∧
  ∃ r : ℕ, ∀ i, ∑ j, (if A i j then 1 else 0) = r

/-- The integral adjacency matrix. -/
def adjacency {d : ℕ} (A : Fin d → Fin d → Bool) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => if A i j then 1 else 0

/-- The integral skew adjacency matrix. -/
def skewAdjacency {d : ℕ} (A : Fin d → Fin d → Bool) : Matrix (Fin d) (Fin d) ℤ :=
  adjacency A - (adjacency A).transpose

/-- The point at which the implicit equation is expanded. -/
noncomputable def z (d : ℕ) : ℂ := 2 / d

/-- The determinant polynomial in the paper. -/
noncomputable def K {d : ℕ} (A : Fin d → Fin d → Bool) (y : Fin d → ℂ) : ℂ :=
  (1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
    (adjacency A).map (Int.castRingHom ℂ)) * diagonal y).det

/-- Append the last coordinate, retaining the paper's vertex order. -/
def appendLast {d : ℕ} (y : Fin (d - 1) → ℂ) (t : ℂ) : Fin d → ℂ :=
  fun i => @Fin.snoc (d - 1) (fun _ => ℂ) y t
    (⟨i.val, by have := i.isLt; omega⟩ : Fin (d - 1 + 1))

/-- The local solution has the stated value, complex C² regularity and equation germ. -/
def IsLocalSolution {d : ℕ} (A : Fin d → Fin d → Bool)
    (h : (Fin (d - 1) → ℂ) → ℂ) : Prop :=
  h (fun _ => z d) = z d ∧
  ContDiffAt ℂ 2 h (fun _ => z d) ∧
  ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), K A (appendLast y (h y)) = 0

/-- The complex-valued phase function on real angular coordinates. -/
noncomputable def phase {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ)
    (θ : Fin (d - 1) → ℝ) : ℂ :=
  Complex.log (h (fun j => z d * Complex.exp (Complex.I * θ j)))

/-- Second real Fréchet derivatives, evaluated in the two coordinate directions. -/
noncomputable def hessian {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ :=
  fun j k => fderiv ℝ (fun θ => fderiv ℝ (phase h) θ (Pi.single j 1)) 0 (Pi.single k 1)

/-- Wormald's Hessian determinant. -/
noncomputable def calH {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ) : ℂ :=
  (hessian h).det

/-- Conjecture 6, including existence and independence of the local solution. -/
def claim : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ A : Fin d → Fin d → Bool, IsRegularTournament A →
    (∃ h, IsLocalSolution A h) ∧
    ∀ h, IsLocalSolution A h → calH h ≠ 0 ∧ ∃ q : ℚ, (d : ℂ) / calH h = (q : ℂ) ^ 2

end D5.S3.Combinatorics.WormaldTournamentHessian.Result
