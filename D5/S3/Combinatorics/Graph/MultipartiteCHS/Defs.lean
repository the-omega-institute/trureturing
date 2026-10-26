/- GID: D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MultipartiteCHS/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum, mathlib/module/Mathlib.RingTheory.MvPolynomial.Symmetric.Defs, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Complete multipartite adjacency matrices and their complete homogeneous symmetric norms. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs

/-- Vertices of the complete multipartite graph with part sizes `a`. -/
abbrev Vtx {r : ℕ} (a : Fin r → ℕ) := Σ i : Fin r, Fin (a i)

/-- Adjacency matrix of the complete multipartite graph: different parts are adjacent. -/
def adj {r : ℕ} (a : Fin r → ℕ) : Matrix (Vtx a) (Vtx a) ℝ :=
  Matrix.of fun x y => if x.1 = y.1 then 0 else 1

theorem adj_isHermitian {r : ℕ} (a : Fin r → ℕ) : (adj a).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro x y
  simp [adj, eq_comm]

/-- The complete homogeneous polynomial of the adjacency eigenvalues. -/
noncomputable def chs {r : ℕ} (a : Fin r → ℕ) (d : ℕ) : ℝ :=
  MvPolynomial.eval (adj_isHermitian a).eigenvalues (MvPolynomial.hsymm (Vtx a) ℝ d)

noncomputable def chsNorm {r : ℕ} (a : Fin r → ℕ) (d : ℕ) : ℝ :=
  chs a d ^ ((1 : ℝ) / d)

def minParts (r n : ℕ) : Fin r → ℕ :=
  fun i => if (i : ℕ) = 0 then n - r + 1 else 1

def balancedParts (r n : ℕ) : Fin r → ℕ :=
  fun i => n / r + if (i : ℕ) < n % r then 1 else 0

/-- Equality of part multisets. -/
def SameParts {r : ℕ} (a b : Fin r → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin r), a = b ∘ σ

def claim : Prop :=
  ∀ (r n m : ℕ), 2 ≤ r → r ≤ n → 1 ≤ m → ∀ a : Fin r → ℕ,
    (∀ i, 0 < a i) → ∑ i, a i = n →
      (chsNorm (minParts r n) (2 * m) ≤ chsNorm a (2 * m) ∧
        (chsNorm a (2 * m) = chsNorm (minParts r n) (2 * m) →
          SameParts a (minParts r n))) ∧
      (chsNorm a (2 * m) ≤ chsNorm (balancedParts r n) (2 * m) ∧
        (chsNorm a (2 * m) = chsNorm (balancedParts r n) (2 * m) →
          SameParts a (balancedParts r n)))

end D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
