/- GID: D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.claim; result=D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.result; claim=D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.claim
   digest: The triangle refutes Li–Guo Conjecture 2.22 on signless Laplacian eigenvalues. -/

/-
admission_basis: open-problem-resolution (#23307; Refuted).
Frozen declaration identities (from the source-matching Lean report):
D1: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind
  statement_id: sha256:3827af1eb14b3504427589ed624d2885edf890b3c9beb1a338e89ef0bf630e07
D2: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.sourceMatrix
  statement_id: sha256:8494c96c2289763860006d56dd8768fdf7477f0c0b187d6e22a611010d1e9331
D3: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphSpectrum
  statement_id: sha256:8291dd1bc1d0040d3639bb40b905a235544695acdae1180a66d04c2470b4cc2b
D4: D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.source_matrix_isHermitian
  statement_id: sha256:0dab7839d261448f5717a90dac6d7793bf90588b6bf86799335cb21107b03899
The rows below refer to those declaration identities, never to a module pin.
TQ and R retain the expressions in #23307; graph matrices and spectra use existing owners.
triangle_matrix: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D2.
  Consumers: triangle_charpoly.
triangle_values: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D2, D3, D4.
  Consumers: result.
triangle_maxDegree: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: triangle_values, result.
TQ: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D3.
  Consumers: claim, triangle_values.
triangle_charpoly: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D2.
  Consumers: triangle_spectrum.
result: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D2, D3, D4.
  Consumers: none.
claim: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D3.
  Consumers: result.
R: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: claim, triangle_values.
triangle_degree: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: triangle_maxDegree, triangle_matrix, triangle_values.
triangle_spectrum: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D1, D2, D3, D4.
  Consumers: triangle_values.
All theorem proofs use upstream application and normalization, with same-module helpers inlined.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The all-orders cycle-family statement is not asserted here.
-/

import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! The triangle has truncated signless spectral square sum 4 and degree bound 3. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.SignlessLaplacian.LiGuoDegreeSequenceRefutation

open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

noncomputable def TQ {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  ((graphSpectrum G .signless).map (fun q => (max (q - 2) 0) ^ 2)).sum

noncomputable def R {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact (1 - 1 / (G.maxDegree : ℝ)) *
    ∑ i : Fin n, (G.degree i : ℝ) * ((G.degree i : ℝ) - 1)

def claim : Prop := by
  classical
  exact ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    0 < G.maxDegree → TQ G ≤ R G

end D5.S3.Combinatorics.Graph.SignlessLaplacian.LiGuoDegreeSequenceRefutation

namespace D5.S3.Combinatorics.Graph.SignlessLaplacian.LiGuoDegreeSequenceRefutation
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open Matrix Polynomial

private theorem triangle_degree (i : Fin 3)
    [Fintype ((SimpleGraph.cycleGraph 3).neighborSet i)] :
    (SimpleGraph.cycleGraph 3).degree i = 2 := by
  have h := SimpleGraph.cycleGraph_degree_three_le (n := 0) (v := i)
  rw [← SimpleGraph.ncard_neighborSet] at h ⊢
  exact h

private theorem triangle_maxDegree [DecidableRel (SimpleGraph.cycleGraph 3).Adj] :
    (SimpleGraph.cycleGraph 3).maxDegree = 2 := by
  apply SimpleGraph.IsRegularOfDegree.maxDegree_eq
  intro v
  exact triangle_degree v

private theorem triangle_matrix : sourceMatrix (SimpleGraph.cycleGraph 3) .signless =
    (!![2, 1, 1; 1, 2, 1; 1, 1, 2] : Matrix (Fin 3) (Fin 3) ℝ) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceMatrix, SimpleGraph.cycleGraph_three_eq_top,
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal,
      SimpleGraph.complete_graph_degree, triangle_degree]

private theorem triangle_charpoly :
    (sourceMatrix (SimpleGraph.cycleGraph 3) .signless).charpoly =
      (X - C (4 : ℝ)) * (X - C (1 : ℝ)) * (X - C (1 : ℝ)) := by
  classical
  rw [triangle_matrix, Matrix.charpoly, Matrix.det_fin_three]
  norm_num [Matrix.charmatrix, Matrix.diagonal, Matrix.sub_apply,
    Matrix.map_apply, Polynomial.C_ofNat]
  ring

private theorem triangle_spectrum :
    graphSpectrum (SimpleGraph.cycleGraph 3) .signless = {4} + {1} + {1} := by
  classical
  have hr : (sourceMatrix (SimpleGraph.cycleGraph 3) .signless).charpoly.roots =
      graphSpectrum (SimpleGraph.cycleGraph 3) .signless :=
    (source_matrix_isHermitian (SimpleGraph.cycleGraph 3) .signless).roots_charpoly_eq_eigenvalues
  rw [← hr, triangle_charpoly]
  rw [Polynomial.roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
    Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp only [Polynomial.roots_X_sub_C]

private theorem triangle_values :
    TQ (SimpleGraph.cycleGraph 3) = 4 ∧ R (SimpleGraph.cycleGraph 3) = 3 := by
  classical
  constructor
  · norm_num [TQ, triangle_spectrum]
  · norm_num [R, triangle_maxDegree, triangle_degree]

theorem result : ¬ claim := by
  classical
  intro h
  obtain ⟨ht, hr⟩ := triangle_values
  have hle := h 3 (SimpleGraph.cycleGraph 3)
    (by simpa only [triangle_maxDegree] using (show 0 < (2 : ℕ) by norm_num))
  rw [ht, hr] at hle
  norm_num at hle


end D5.S3.Combinatorics.Graph.SignlessLaplacian.LiGuoDegreeSequenceRefutation
