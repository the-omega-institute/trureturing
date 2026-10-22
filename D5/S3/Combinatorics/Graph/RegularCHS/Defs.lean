/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum, mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant, mathlib/module/Mathlib.RingTheory.MvPolynomial.Symmetric.Defs]
   utility: none
   digest: Complete homogeneous symmetric adjacency coefficients and regular graph extrema. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

noncomputable section
open Classical

namespace D5.S3.Combinatorics.Graph.RegularCHS.Defs

/-- A real adjacency matrix is Hermitian. -/
theorem adjMatrix_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix

open Classical in
/-- The complete homogeneous coefficient of the adjacency eigenvalues. -/
noncomputable def chs {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : ℝ :=
  MvPolynomial.eval (Matrix.IsHermitian.eigenvalues
    (A := G.adjMatrix ℝ) (adjMatrix_isHermitian G)) (MvPolynomial.hsymm (Fin n) ℝ d)

/-- The adjacency CHS norm in degree `d`. -/
noncomputable def chsNorm {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : ℝ :=
  chs G d ^ ((1 : ℝ) / d)

/-- The cycle and the complete graph attain the regular connected extrema. -/
def claim : Prop :=
  ∀ (n m : ℕ), 3 ≤ n → 1 ≤ m →
    ((SimpleGraph.cycleGraph n).Connected ∧
      (∃ r, (SimpleGraph.cycleGraph n).IsRegularOfDegree r) ∧
      (⊤ : SimpleGraph (Fin n)).Connected ∧
      (∃ r, (⊤ : SimpleGraph (Fin n)).IsRegularOfDegree r)) ∧
    ∀ G : SimpleGraph (Fin n), G.Connected → (∃ r, G.IsRegularOfDegree r) →
      chsNorm (SimpleGraph.cycleGraph n) (2 * m) ≤ chsNorm G (2 * m) ∧
        chsNorm G (2 * m) ≤ chsNorm (⊤ : SimpleGraph (Fin n)) (2 * m)

end D5.S3.Combinatorics.Graph.RegularCHS.Defs
