/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact SF and the connected/disconnected beta dichotomy for Heawood double lifts. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
import D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodMatching
import D5.S1.Eigenstructure.BinaryTraceZeroSimilarity

/-! The six-type parameter transfer in HEAWOOD_DOUBLE_COVER_GAIN,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
open StarFormingDissociationRefutation HeawoodSwitching HeawoodLift
open D5.S3.Combinatorics.Graph.StarForming.Families

open D5.S1.Eigenstructure.BinaryTraceZeroSimilarity

-- The columns are the basis vectors in their original Fano coordinates.
private def basisMatrix (k : Fin 6) : Mat :=
  if k = 0 then !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  else if k = 1 then !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  else !![1, 0, 0; 0, 0, 1; 0, 1, 0]

private def basisUnit (k : Fin 6) : Matˣ where
  val := basisMatrix k
  inv := (basisMatrix k).transpose
  val_inv := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl
  inv_val := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

private def firstFlag (k : Fin 6) : F2 := if k = 5 then 1 else 0
private def diagonal (k : Fin 6) : F2 := if k = 2 ∨ k = 3 then 1 else 0

private theorem representative_in_basis (k : Fin 6) :
    representative k = (basisUnit k : Mat) *
      HeawoodMatching.gain (firstFlag k) (diagonal k)
        (if k = 4 ∨ k = 5 then 1 else 0) (if k = 3 then 1 else 0)
        (if k = 1 ∨ k = 4 ∨ k = 5 then 1 else 0) *
      (↑(basisUnit k)⁻¹ : Mat) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

/-- Connected binary Heawood lifts have beta fifteen or sixteen. -/
theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) :
    15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16 := by
  obtain ⟨k, g, hg⟩ := exists_conjugate (phi s) ((HeawoodLift.preconnected_iff s).mp hs)
    (trace_phi s)
  rw [representative_in_basis] at hg
  have bounds := HeawoodMatching.beta_bounds s (g * basisUnit k) (firstFlag k) (diagonal k)
    (if k = 4 ∨ k = 5 then 1 else 0) (if k = 3 then 1 else 0)
    (if k = 1 ∨ k = 4 ∨ k = 5 then 1 else 0)
    (by simpa only [mul_inv_rev, Units.val_mul, mul_assoc] using hg)
  have lower := bounds.1
  have atLeastOne : ∀ k : Fin 6, firstFlag k = 0 ∨ firstFlag k + diagonal k = 1 := by
    decide +kernel
  constructor
  · rcases atLeastOne k with h | h
    · rw [ite_eq_left h] at lower
      omega
    · rw [ite_eq_left h] at lower
      omega
  · exact bounds.2

/-- The complete two-sheet dichotomy uses actual connectedness and finite maxima. -/
theorem parameters (s : Signing) :
    SF (graph s) 2=16 ∧
    (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧
    ((graph s).Preconnected →
      (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1) := by
  classical
  refine ⟨sf_all s,⟨?_,disconnected_beta s⟩,?_⟩
  · intro hb hc
    have h := (connected_beta s hc).1
    omega
  · intro hc
    have hb := connected_beta s hc
    rw [sf_all]
    omega

end D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
