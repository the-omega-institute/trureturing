/- GID: D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.claim; result=D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result; claim=D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.claim
   digest: A bad potential on the eight-cycle has only scalar shared symmetries. -/

/-
proof_shape: potential_bad: content; scalar_commutant: bind-only; result: content.
escape_witness: potential_bad (all-couplings nodal eigenvector);
  scalar_commutant: none;
  result (potential_bad on its live proof path).
scalar_commutant: bind-only; consumer: result.
cycle8_lap: bind-only; consumer: scalar_commutant.
admission_basis: open-problem-resolution (#13591; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

set_option autoImplicit false
set_option maxRecDepth 4096

open Matrix

namespace D5.S3.Combinatorics.Graph.AndersonSymmetryConverseRefutation

/-- Every nonzero eigenvector is nonzero at every vertex. -/
def nonvanishingEigenvectors {L : ℕ} (H : Matrix (Fin L) (Fin L) ℂ) : Prop :=
  ∀ (μ : ℂ) (z : Fin L → ℂ), z ≠ 0 → H *ᵥ z = μ • z → ∀ j, z j ≠ 0

/-- Definition 1.1: at every real coupling at least one of the two conditions fails. -/
def bad {L : ℕ} (v : Fin L → ℝ) : Prop :=
  ∀ t : ℝ, ¬ ((∀ μ : ℂ,
      ((SimpleGraph.cycleGraph L).lapMatrix ℂ +
        (t : ℂ) • Matrix.diagonal (fun j => (v j : ℂ))).charpoly.IsRoot μ →
      ((SimpleGraph.cycleGraph L).lapMatrix ℂ +
        (t : ℂ) • Matrix.diagonal (fun j => (v j : ℂ))).charpoly.rootMultiplicity μ = 1) ∧
    nonvanishingEigenvectors ((SimpleGraph.cycleGraph L).lapMatrix ℂ +
      (t : ℂ) • Matrix.diagonal (fun j => (v j : ℂ))))

/-- An orthogonal shared symmetry other than the two scalar symmetries. -/
def sharedSymmetry {L : ℕ} (v : Fin L → ℝ) : Prop :=
  ∃ O : Matrix (Fin L) (Fin L) ℝ, O ∈ Matrix.orthogonalGroup (Fin L) ℝ ∧
    O ≠ 1 ∧ O ≠ -1 ∧
    O * (SimpleGraph.cycleGraph L).lapMatrix ℝ =
      (SimpleGraph.cycleGraph L).lapMatrix ℝ * O ∧
    O * Matrix.diagonal v = Matrix.diagonal v * O

/-- LG-CONV, the one-dimensional two-valued instance of the published question. -/
def claim : Prop :=
  ∀ (L : ℕ), 2 < L → ∀ v : Fin L → ℝ,
    (∀ j, v j = -1 ∨ v j = 1) → bad v → sharedSymmetry v

private def potential : Fin 8 → ℝ := ![1, 1, 1, 1, -1, 1, -1, -1]

-- proof_shape: bind-only; consumer: scalar_commutant.
private theorem cycle8_lap : (SimpleGraph.cycleGraph 8).lapMatrix ℝ =
    !![2,-1,0,0,0,0,0,-1; -1,2,-1,0,0,0,0,0; 0,-1,2,-1,0,0,0,0;
       0,0,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
       0,0,0,0,0,-1,2,-1; -1,0,0,0,0,0,-1,2] := by
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    SimpleGraph.cycleGraph_degree_three_le]
  fin_cases i <;> fin_cases j <;> norm_num [SimpleGraph.adjMatrix, SimpleGraph.cycleGraph,
    Matrix.diagonal, Matrix.of_apply, Fin.ext_iff, Fin.sub_def]

-- proof_shape: content; escape_witness: all-couplings nodal eigenvector; consumer: result.
private theorem potential_bad : bad potential := by
  intro t h
  let a : ℝ := Real.sqrt (t ^ 2 + 2) - t
  have aq : a ^ 2 + 2 * t * a - 2 = 0 := by
    have hs := Real.sq_sqrt (show 0 ≤ t ^ 2 + 2 by positivity)
    dsimp [a]
    nlinarith
  have aqc : (a : ℂ) ^ 2 + 2 * (t : ℂ) * (a : ℂ) - 2 = 0 := by
    exact_mod_cast aq
  let z : Fin 8 → ℂ := ![1, 0, -1, (a : ℂ), 1 - (a : ℂ) ^ 2,
    -2 * (t : ℂ), 1, -(a : ℂ)]
  have hz : z ≠ 0 := by
    intro hzero
    have := congrFun hzero 0
    norm_num [z] at this
  have heig : ((SimpleGraph.cycleGraph 8).lapMatrix ℂ +
      (t : ℂ) • Matrix.diagonal (fun j => (potential j : ℂ))) *ᵥ z =
      (2 + (a : ℂ) + (t : ℂ)) • z := by
    ext j
    fin_cases j <;> norm_num [Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_diagonal, SimpleGraph.lapMatrix_mulVec_apply,
      SimpleGraph.cycleGraph_degree_three_le, SimpleGraph.cycleGraph_neighborFinset,
      z, potential, Fin.add_def, Fin.sub_def, Fin.neg_def,
      show (-1 : Fin 8) = 7 by decide, Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
    · rw [Finset.sum_pair (show (-1 : Fin 8) ≠ 1 by decide)]
      change 2 - (-(a : ℂ) + 0) = 2 + (a : ℂ)
      ring
    all_goals solve | ring | linear_combination aqc | linear_combination -aqc |
      linear_combination (a : ℂ) * aqc
  exact (h.2 (2 + (a : ℂ) + (t : ℂ)) z hz heig 1) (by norm_num [z])

-- proof_shape: bind-only; escape_witness: none; consumer: result.
set_option maxHeartbeats 2000000 in
private theorem scalar_commutant (O : Matrix (Fin 8) (Fin 8) ℝ)
    (hD : O * (SimpleGraph.cycleGraph 8).lapMatrix ℝ =
      (SimpleGraph.cycleGraph 8).lapMatrix ℝ * O)
    (hV : O * Matrix.diagonal potential = Matrix.diagonal potential * O) :
    O = O 0 0 • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  have d00 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨0, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨0, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d00
  have d01 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨1, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨1, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d01
  have d02 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨2, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨2, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d02
  have d03 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨3, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨3, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d03
  have d04 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨4, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨4, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d04
  have d05 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨5, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨5, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d05
  have d06 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (2 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨6, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨6, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d06
  have d07 : O ⟨0, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨0, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨0, by decide⟩ ⟨7, by decide⟩ * (2 : ℝ)))))))) =
      (2 : ℝ) * O ⟨0, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨7, by decide⟩ ⟨7, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨7, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d07
  have d10 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (2 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨0, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨0, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨0, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d10
  have d11 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (2 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨1, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨1, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨1, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp
  norm_num at d11
  have d12 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (2 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨2, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨2, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨2, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d12
  have d13 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (2 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨3, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨3, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨3, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d13
  have d14 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (2 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨4, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨4, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨4, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d14
  have d15 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (2 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨5, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨5, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨5, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d15
  have d17 : O ⟨1, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨1, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨1, by decide⟩ ⟨7, by decide⟩ * (2 : ℝ)))))))) =
      (-1 : ℝ) * O ⟨0, by decide⟩ ⟨7, by decide⟩ + ((2 : ℝ) * O ⟨1, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨7, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨7, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d17
  have d20 : O ⟨2, by decide⟩ ⟨0, by decide⟩ * (2 : ℝ) + (O ⟨2, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨0, by decide⟩ + ((2 : ℝ) * O ⟨2, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨0, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨0, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d20
  have d21 : O ⟨2, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨1, by decide⟩ * (2 : ℝ) + (O ⟨2, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨1, by decide⟩ + ((2 : ℝ) * O ⟨2, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨1, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨1, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d21
  have d22 : O ⟨2, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨2, by decide⟩ * (2 : ℝ) + (O ⟨2, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨2, by decide⟩ + ((2 : ℝ) * O ⟨2, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨2, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨2, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d22
  have d23 : O ⟨2, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨3, by decide⟩ * (2 : ℝ) + (O ⟨2, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨3, by decide⟩ + ((2 : ℝ) * O ⟨2, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨3, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨3, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d23
  have d24 : O ⟨2, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨4, by decide⟩ * (2 : ℝ) + (O ⟨2, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨4, by decide⟩ + ((2 : ℝ) * O ⟨2, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨4, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨4, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d24
  have d25 : O ⟨2, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨2, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨5, by decide⟩ * (2 : ℝ) + (O ⟨2, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨2, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨1, by decide⟩ ⟨5, by decide⟩ + ((2 : ℝ) * O ⟨2, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨4, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨5, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨5, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d25
  have d34 : O ⟨3, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨3, by decide⟩ ⟨4, by decide⟩ * (2 : ℝ) + (O ⟨3, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨3, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨4, by decide⟩ + ((2 : ℝ) * O ⟨3, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨4, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨4, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨3, by decide⟩ ⟨4, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d34
  have d36 : O ⟨3, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨3, by decide⟩ ⟨6, by decide⟩ * (2 : ℝ) + (O ⟨3, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨6, by decide⟩ + ((2 : ℝ) * O ⟨3, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨4, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨6, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨3, by decide⟩ ⟨6, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d36
  have d37 : O ⟨3, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨3, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨3, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨3, by decide⟩ ⟨7, by decide⟩ * (2 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨2, by decide⟩ ⟨7, by decide⟩ + ((2 : ℝ) * O ⟨3, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨4, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨5, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨7, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨3, by decide⟩ ⟨7, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d37
  have d40 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (2 : ℝ) + (O ⟨4, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨0, by decide⟩ + ((2 : ℝ) * O ⟨4, by decide⟩ ⟨0, by decide⟩ + ((-1 : ℝ) * O ⟨5, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨0, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨0, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨0, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d40
  have d41 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨1, by decide⟩ * (2 : ℝ) + (O ⟨4, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨1, by decide⟩ + ((2 : ℝ) * O ⟨4, by decide⟩ ⟨1, by decide⟩ + ((-1 : ℝ) * O ⟨5, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨1, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨1, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨1, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d41
  have d42 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨1, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨2, by decide⟩ * (2 : ℝ) + (O ⟨4, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨2, by decide⟩ + ((2 : ℝ) * O ⟨4, by decide⟩ ⟨2, by decide⟩ + ((-1 : ℝ) * O ⟨5, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨2, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨2, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨2, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d42
  have d43 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨2, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨3, by decide⟩ * (2 : ℝ) + (O ⟨4, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨3, by decide⟩ + ((2 : ℝ) * O ⟨4, by decide⟩ ⟨3, by decide⟩ + ((-1 : ℝ) * O ⟨5, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨3, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨3, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨3, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d43
  have d45 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨5, by decide⟩ * (2 : ℝ) + (O ⟨4, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨5, by decide⟩ + ((2 : ℝ) * O ⟨4, by decide⟩ ⟨5, by decide⟩ + ((-1 : ℝ) * O ⟨5, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨5, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨5, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨5, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d45
  have d46 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨4, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨4, by decide⟩ ⟨6, by decide⟩ * (2 : ℝ) + (O ⟨4, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨3, by decide⟩ ⟨6, by decide⟩ + ((2 : ℝ) * O ⟨4, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨5, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨6, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨6, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨6, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d46
  have d54 : O ⟨5, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨3, by decide⟩ * (-1 : ℝ) + (O ⟨5, by decide⟩ ⟨4, by decide⟩ * (2 : ℝ) + (O ⟨5, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨5, by decide⟩ ⟨6, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨7, by decide⟩ * (0 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨4, by decide⟩ ⟨4, by decide⟩ + ((2 : ℝ) * O ⟨5, by decide⟩ ⟨4, by decide⟩ + ((-1 : ℝ) * O ⟨6, by decide⟩ ⟨4, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨4, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨5, by decide⟩ ⟨4, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d54
  have d56 : O ⟨5, by decide⟩ ⟨0, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨5, by decide⟩ * (-1 : ℝ) + (O ⟨5, by decide⟩ ⟨6, by decide⟩ * (2 : ℝ) + (O ⟨5, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨4, by decide⟩ ⟨6, by decide⟩ + ((2 : ℝ) * O ⟨5, by decide⟩ ⟨6, by decide⟩ + ((-1 : ℝ) * O ⟨6, by decide⟩ ⟨6, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨6, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨5, by decide⟩ ⟨6, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d56
  have d57 : O ⟨5, by decide⟩ ⟨0, by decide⟩ * (-1 : ℝ) + (O ⟨5, by decide⟩ ⟨1, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨2, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨3, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨4, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨5, by decide⟩ * (0 : ℝ) + (O ⟨5, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) + (O ⟨5, by decide⟩ ⟨7, by decide⟩ * (2 : ℝ)))))))) =
      (0 : ℝ) * O ⟨0, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨1, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨2, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨3, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨4, by decide⟩ ⟨7, by decide⟩ + ((2 : ℝ) * O ⟨5, by decide⟩ ⟨7, by decide⟩ + ((-1 : ℝ) * O ⟨6, by decide⟩ ⟨7, by decide⟩ + ((0 : ℝ) * O ⟨7, by decide⟩ ⟨7, by decide⟩))))))) := by
    have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨5, by decide⟩ ⟨7, by decide⟩) hD
    rw [cycle8_lap] at h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at h
    change Fin 8 → Fin 8 → ℝ at O
    convert h using 1 <;> simp [Fin.succ]
  norm_num at d57
  have v04 : O ⟨0, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨0, by decide⟩ ⟨4, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨4, by decide⟩) hV
  norm_num at v04
  have v06 : O ⟨0, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨0, by decide⟩ ⟨6, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨6, by decide⟩) hV
  norm_num at v06
  have v07 : O ⟨0, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨0, by decide⟩ ⟨7, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨0, by decide⟩ ⟨7, by decide⟩) hV
  norm_num at v07
  have v14 : O ⟨1, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨1, by decide⟩ ⟨4, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨4, by decide⟩) hV
  norm_num at v14
  have v16 : O ⟨1, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨1, by decide⟩ ⟨6, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨6, by decide⟩) hV
  norm_num at v16
  have v17 : O ⟨1, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨1, by decide⟩ ⟨7, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨1, by decide⟩ ⟨7, by decide⟩) hV
  norm_num at v17
  have v24 : O ⟨2, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨2, by decide⟩ ⟨4, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨4, by decide⟩) hV
  norm_num at v24
  have v26 : O ⟨2, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨2, by decide⟩ ⟨6, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨6, by decide⟩) hV
  norm_num at v26
  have v27 : O ⟨2, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨2, by decide⟩ ⟨7, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨2, by decide⟩ ⟨7, by decide⟩) hV
  norm_num at v27
  have v34 : O ⟨3, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨3, by decide⟩ ⟨4, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨3, by decide⟩ ⟨4, by decide⟩) hV
  norm_num at v34
  have v36 : O ⟨3, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨3, by decide⟩ ⟨6, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨3, by decide⟩ ⟨6, by decide⟩) hV
  norm_num at v36
  have v37 : O ⟨3, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨3, by decide⟩ ⟨7, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨3, by decide⟩ ⟨7, by decide⟩) hV
  norm_num at v37
  have v40 : O ⟨4, by decide⟩ ⟨0, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨4, by decide⟩ ⟨0, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨0, by decide⟩) hV
  norm_num at v40
  have v41 : O ⟨4, by decide⟩ ⟨1, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨4, by decide⟩ ⟨1, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨1, by decide⟩) hV
  norm_num at v41
  have v42 : O ⟨4, by decide⟩ ⟨2, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨4, by decide⟩ ⟨2, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨2, by decide⟩) hV
  norm_num at v42
  have v43 : O ⟨4, by decide⟩ ⟨3, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨4, by decide⟩ ⟨3, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨3, by decide⟩) hV
  norm_num at v43
  have v45 : O ⟨4, by decide⟩ ⟨5, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨4, by decide⟩ ⟨5, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨4, by decide⟩ ⟨5, by decide⟩) hV
  norm_num at v45
  have v54 : O ⟨5, by decide⟩ ⟨4, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨5, by decide⟩ ⟨4, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨5, by decide⟩ ⟨4, by decide⟩) hV
  norm_num at v54
  have v56 : O ⟨5, by decide⟩ ⟨6, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨5, by decide⟩ ⟨6, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨5, by decide⟩ ⟨6, by decide⟩) hV
  norm_num at v56
  have v57 : O ⟨5, by decide⟩ ⟨7, by decide⟩ * (-1 : ℝ) = (1 : ℝ) * O ⟨5, by decide⟩ ⟨7, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨5, by decide⟩ ⟨7, by decide⟩) hV
  norm_num at v57
  have v60 : O ⟨6, by decide⟩ ⟨0, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨6, by decide⟩ ⟨0, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨6, by decide⟩ ⟨0, by decide⟩) hV
  norm_num at v60
  have v61 : O ⟨6, by decide⟩ ⟨1, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨6, by decide⟩ ⟨1, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨6, by decide⟩ ⟨1, by decide⟩) hV
  norm_num at v61
  have v62 : O ⟨6, by decide⟩ ⟨2, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨6, by decide⟩ ⟨2, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨6, by decide⟩ ⟨2, by decide⟩) hV
  norm_num at v62
  have v63 : O ⟨6, by decide⟩ ⟨3, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨6, by decide⟩ ⟨3, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨6, by decide⟩ ⟨3, by decide⟩) hV
  norm_num at v63
  have v65 : O ⟨6, by decide⟩ ⟨5, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨6, by decide⟩ ⟨5, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨6, by decide⟩ ⟨5, by decide⟩) hV
  norm_num at v65
  have v70 : O ⟨7, by decide⟩ ⟨0, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨7, by decide⟩ ⟨0, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨7, by decide⟩ ⟨0, by decide⟩) hV
  norm_num at v70
  have v71 : O ⟨7, by decide⟩ ⟨1, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨7, by decide⟩ ⟨1, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨7, by decide⟩ ⟨1, by decide⟩) hV
  norm_num at v71
  have v72 : O ⟨7, by decide⟩ ⟨2, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨7, by decide⟩ ⟨2, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨7, by decide⟩ ⟨2, by decide⟩) hV
  norm_num at v72
  have v73 : O ⟨7, by decide⟩ ⟨3, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨7, by decide⟩ ⟨3, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨7, by decide⟩ ⟨3, by decide⟩) hV
  norm_num at v73
  have v75 : O ⟨7, by decide⟩ ⟨5, by decide⟩ * (1 : ℝ) = (-1 : ℝ) * O ⟨7, by decide⟩ ⟨5, by decide⟩ := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, potential] using
      congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M ⟨7, by decide⟩ ⟨5, by decide⟩) hV
  norm_num at v75
  change Fin 8 → Fin 8 → ℝ at O
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.smul_apply, Matrix.one_apply, Fin.ofNat]
  · linear_combination -1 * d00 + (1 / 2 : ℝ) * v70 + (1 / 2 : ℝ) * v16 + -1 * d17 + (-1 / 2 : ℝ) * v27
  · linear_combination -1 * d03 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v73 + -1 * d14 + -1 * d05 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (1 / 2 : ℝ) * v75
  · linear_combination -1 * d02 + (1 / 2 : ℝ) * v72 + -1 * d11 + -1 * d46 + (-1 / 2 : ℝ) * v45 + -1 * d37 + -1 * d20 + (-1 / 2 : ℝ) * v56
  · linear_combination (-1 / 2 : ℝ) * v04
  · linear_combination 1 * d02 + -1 * d00 + 1 * d24 + 1 * d13 + 1 * d15 + (1 / 2 : ℝ) * v34 + (-1 / 2 : ℝ) * v14 + (-1 / 2 : ℝ) * v72 + (1 / 2 : ℝ) * v70 + -1 * d17 + (-1 / 2 : ℝ) * v27
  · linear_combination (-1 / 2 : ℝ) * v06
  · linear_combination (-1 / 2 : ℝ) * v07
  · linear_combination (-1 / 2 : ℝ) * v07 + (1 / 2 : ℝ) * v16 + -1 * d17 + (-1 / 2 : ℝ) * v27
  · linear_combination -1 * d03 + 1 * d01 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v73 + -1 * d14 + -1 * d05 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (1 / 2 : ℝ) * v75 + (-1 / 2 : ℝ) * v71
  · linear_combination -1 * d11 + -1 * d00 + (1 / 2 : ℝ) * v16 + -1 * d46 + (-1 / 2 : ℝ) * v45 + -1 * d37 + -1 * d20 + (-1 / 2 : ℝ) * v56 + -1 * d17 + (-1 / 2 : ℝ) * v27 + (1 / 2 : ℝ) * v70
  · linear_combination -1 * d14 + -1 * d05 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (1 / 2 : ℝ) * v75
  · linear_combination (-1 / 2 : ℝ) * v14
  · linear_combination 1 * d05 + (-1 / 2 : ℝ) * v04 + (-1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v75
  · linear_combination (-1 / 2 : ℝ) * v16
  · linear_combination (-1 / 2 : ℝ) * v17
  · linear_combination 1 * d10 + -1 * d03 + (1 / 2 : ℝ) * v04 + (-1 / 2 : ℝ) * v17 + -1 * d14 + 1 * d01 + -1 * d05 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v71 + (1 / 2 : ℝ) * v75 + (1 / 2 : ℝ) * v73
  · linear_combination (-1 / 2 : ℝ) * v07 + (1 / 2 : ℝ) * v16 + -1 * d46 + (-1 / 2 : ℝ) * v45 + -1 * d37 + -1 * d20 + (-1 / 2 : ℝ) * v56 + -1 * d17 + (-1 / 2 : ℝ) * v27
  · linear_combination -1 * d14 + 1 * d01 + -1 * d05 + (1 / 2 : ℝ) * v06 + 1 * d12 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v71 + (1 / 2 : ℝ) * v75
  · linear_combination -1 * d17 + 1 * d02 + (-1 / 2 : ℝ) * v14 + (1 / 2 : ℝ) * v16 + 1 * d13 + -1 * d00 + (-1 / 2 : ℝ) * v27 + (-1 / 2 : ℝ) * v72 + (1 / 2 : ℝ) * v70
  · linear_combination (-1 / 2 : ℝ) * v24
  · linear_combination -1 * d24 + 1 * d17 + -1 * d02 + (-1 / 2 : ℝ) * v16 + -1 * d13 + 1 * d00 + (1 / 2 : ℝ) * v27 + (-1 / 2 : ℝ) * v34 + (-1 / 2 : ℝ) * v70 + (1 / 2 : ℝ) * v72
  · linear_combination (-1 / 2 : ℝ) * v26
  · linear_combination (-1 / 2 : ℝ) * v27
  · linear_combination -1 * d46 + (-1 / 2 : ℝ) * v45 + -1 * d37 + (-1 / 2 : ℝ) * v56 + (-1 / 2 : ℝ) * v27
  · linear_combination 1 * d21 + 1 * d10 + (-1 / 2 : ℝ) * v17 + -1 * d14 + 1 * d01 + -1 * d05 + (1 / 2 : ℝ) * v06 + 1 * d12 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v71 + (1 / 2 : ℝ) * v75
  · linear_combination 1 * d22 + 1 * d11 + (-1 / 2 : ℝ) * v07 + -1 * d17 + 1 * d02 + (-1 / 2 : ℝ) * v14 + (1 / 2 : ℝ) * v16 + 1 * d13 + (-1 / 2 : ℝ) * v27 + (-1 / 2 : ℝ) * v72
  · linear_combination 1 * d23 + 1 * d01 + 1 * d12 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v71
  · linear_combination (-1 / 2 : ℝ) * v34
  · linear_combination 1 * d25 + -1 * d05 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v26 + (1 / 2 : ℝ) * v75
  · linear_combination (-1 / 2 : ℝ) * v36
  · linear_combination (-1 / 2 : ℝ) * v37
  · linear_combination (1 / 2 : ℝ) * v40
  · linear_combination (1 / 2 : ℝ) * v41
  · linear_combination (1 / 2 : ℝ) * v42
  · linear_combination (1 / 2 : ℝ) * v43
  · linear_combination 1 * d34 + 1 * d23 + 1 * d01 + 1 * d12 + 1 * d25 + -1 * d05 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v26 + (-1 / 2 : ℝ) * v71 + (1 / 2 : ℝ) * v75
  · linear_combination (1 / 2 : ℝ) * v45
  · linear_combination 1 * d36 + 1 * d25 + -1 * d05 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v37 + (1 / 2 : ℝ) * v75
  · linear_combination (-1 / 2 : ℝ) * v36 + -1 * d46 + (-1 / 2 : ℝ) * v45 + (-1 / 2 : ℝ) * v56
  · linear_combination 1 * d40 + (1 / 2 : ℝ) * v27 + (1 / 2 : ℝ) * v41 + 1 * d37 + (-1 / 2 : ℝ) * v36
  · linear_combination 1 * d41 + -1 * d21 + -1 * d10 + (1 / 2 : ℝ) * v17 + 1 * d14 + -1 * d01 + 1 * d05 + (-1 / 2 : ℝ) * v06 + -1 * d12 + (1 / 2 : ℝ) * v24 + (1 / 2 : ℝ) * v40 + (1 / 2 : ℝ) * v42 + (1 / 2 : ℝ) * v71 + (-1 / 2 : ℝ) * v75
  · linear_combination 1 * d42 + -1 * d22 + -1 * d11 + (1 / 2 : ℝ) * v07 + 1 * d17 + -1 * d02 + (1 / 2 : ℝ) * v14 + (-1 / 2 : ℝ) * v16 + -1 * d13 + (1 / 2 : ℝ) * v27 + (1 / 2 : ℝ) * v41 + (1 / 2 : ℝ) * v43 + (1 / 2 : ℝ) * v72
  · linear_combination 1 * d43 + (1 / 2 : ℝ) * v42 + 1 * d34 + 1 * d25 + -1 * d05 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v26 + (1 / 2 : ℝ) * v75
  · linear_combination (-1 / 2 : ℝ) * v54
  · linear_combination 1 * d45 + 1 * d34 + 1 * d23 + 1 * d01 + 1 * d12 + 1 * d36 + 1 * d25 + -1 * d05 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v24 + (-1 / 2 : ℝ) * v37 + (-1 / 2 : ℝ) * v71 + (1 / 2 : ℝ) * v75
  · linear_combination (-1 / 2 : ℝ) * v56
  · linear_combination (-1 / 2 : ℝ) * v57
  · linear_combination (1 / 2 : ℝ) * v60
  · linear_combination (1 / 2 : ℝ) * v61
  · linear_combination (1 / 2 : ℝ) * v62
  · linear_combination (1 / 2 : ℝ) * v63
  · linear_combination 1 * d54 + 1 * d43 + (1 / 2 : ℝ) * v42 + 1 * d45 + 1 * d34 + 1 * d36 + 1 * d25 + -1 * d05 + (1 / 2 : ℝ) * v04 + (1 / 2 : ℝ) * v06 + (-1 / 2 : ℝ) * v37 + (1 / 2 : ℝ) * v75
  · linear_combination (1 / 2 : ℝ) * v65
  · linear_combination 1 * d56 + 1 * d45 + 1 * d34 + 1 * d23 + 1 * d01 + 1 * d12 + (-1 / 2 : ℝ) * v57 + (-1 / 2 : ℝ) * v71
  · linear_combination 1 * d57 + 1 * d40 + (1 / 2 : ℝ) * v41 + 1 * d46 + (1 / 2 : ℝ) * v45 + 1 * d37 + (1 / 2 : ℝ) * v27
  · linear_combination (1 / 2 : ℝ) * v70
  · linear_combination (1 / 2 : ℝ) * v71
  · linear_combination (1 / 2 : ℝ) * v72
  · linear_combination (1 / 2 : ℝ) * v73
  · linear_combination -1 * d46 + (-1 / 2 : ℝ) * v45 + -1 * d37 + -1 * d20 + 1 * d04 + -1 * d11 + (-1 / 2 : ℝ) * v56 + 1 * d24 + -1 * d17 + 1 * d13 + -1 * d00 + 1 * d15 + (-1 / 2 : ℝ) * v27 + (1 / 2 : ℝ) * v34 + (1 / 2 : ℝ) * v70
  · linear_combination (1 / 2 : ℝ) * v75
  · linear_combination 1 * d24 + -1 * d17 + 1 * d02 + (1 / 2 : ℝ) * v16 + 1 * d13 + -1 * d00 + 1 * d15 + (-1 / 2 : ℝ) * v07 + 1 * d06 + (-1 / 2 : ℝ) * v14 + (-1 / 2 : ℝ) * v27 + (1 / 2 : ℝ) * v34 + (1 / 2 : ℝ) * v70 + (-1 / 2 : ℝ) * v72
  · linear_combination 1 * d07 + (-1 / 2 : ℝ) * v06 + (1 / 2 : ℝ) * v17

/-- The potential (1,1,1,1,-1,1,-1,-1) refutes LG-CONV on the eight-cycle. -/
theorem result : ¬ claim := by
  intro hc
  have hv : ∀ j, potential j = -1 ∨ potential j = 1 := by
    intro j
    fin_cases j <;> norm_num [potential]
  obtain ⟨O, hO, hn, hneg, hD, hV⟩ := hc 8 (by norm_num) potential hv potential_bad
  have hs := scalar_commutant O hD hV
  have hsq : (O 0 0) ^ 2 = 1 := by
    have ho := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 0 0)
      ((Matrix.mem_orthogonalGroup_iff' (Fin 8) ℝ).mp hO)
    rw [hs] at ho
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.one_apply] at ho
    nlinarith
  rcases (sq_eq_one_iff).mp hsq with hpos | hminus
  · apply hn
    rw [hs, hpos]
    simp
  · apply hneg
    rw [hs, hminus]
    simp

#print axioms result

end D5.S3.Combinatorics.Graph.AndersonSymmetryConverseRefutation
