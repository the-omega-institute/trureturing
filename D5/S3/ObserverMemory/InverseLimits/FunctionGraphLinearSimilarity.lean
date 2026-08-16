/- GID: D5/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two eight-state transition matrices admit an explicit integral similarity. -/

import D5.S3.ObserverMemory.InverseLimits.FunctionGraphSpectrumCollision

/- Library-search audit trail (2026-08-16):
   * D5 searches found no transition-matrix similarity theorem beyond the frozen spectrum
     collision module imported here.
   * Pinned Mathlib provides the matrix unit interface and finite matrix multiplication, but no
     theorem identifying these two repository-defined maps.
   * A GitHub Lean-code search for the intertwining equation found no exact reusable result. -/

namespace D5.S3.ObserverMemory.InverseLimits.FunctionGraphLinearSimilarity

open D5.S3.ObserverMemory.InverseLimits.FunctionGraphSpectrumCollision

/-- The integral transition matrix whose `j`-th column is the basis vector indexed by `f j`. -/
def transitionMatrix (f : Fin 8 -> Fin 8) : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => if f j = i then 1 else 0

/-- An explicit integral change of basis intertwining the transition matrices of `tauA` and
`tauB`. -/
def similarityWitness : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 1]

private def similarityWitnessInv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

private def similarityWitnessUnit : (Matrix (Fin 8) (Fin 8) ℤ)ˣ where
  val := similarityWitness
  inv := similarityWitnessInv
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [similarityWitness, similarityWitnessInv, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [similarityWitness, similarityWitnessInv, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The transition matrices of the two source maps are linearly similar over the integers. -/
theorem transition_matrices_linearly_similar :
    Exists fun P : Matrix (Fin 8) (Fin 8) ℤ =>
      IsUnit P /\ transitionMatrix tauA * P = P * transitionMatrix tauB := by
  refine ⟨similarityWitness, similarityWitnessUnit.isUnit, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transitionMatrix, tauA, tauB, similarityWitness, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> decide

example : Unit := ()

example : Nonempty (Matrix (Fin 8) (Fin 8) ℤ) := ⟨0⟩

#print axioms transition_matrices_linearly_similar

end D5.S3.ObserverMemory.InverseLimits.FunctionGraphLinearSimilarity
