/- GID: D5/S3/Quantum/Measurement/Auric/TiltedPermutationGram
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/TiltedPermutationGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent Choi blocks of the allowed tilted and permuted protocols. -/

import D5.S3.Quantum.Measurement.Auric.TiltedSymmetries
import D5.S3.Quantum.Measurement.Auric.CoherentSlack

/-! # Coherent Choi blocks of the allowed tilted and permuted protocols -/

namespace D5.S3.Quantum.Measurement.Auric.TiltedPermutationGram

open _root_.Matrix
open D5.S3.Quantum.Measurement.Auric.TiltedInstrument
open D5.S3.Quantum.Measurement.Auric.TiltedSymmetries
open D5.S3.Quantum.Measurement.Auric.CoherentSlack

private def exchangeSectors : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

private def exchangePairs : Equiv.Perm (Fin 5) :=
  (Equiv.swap 0 1).trans (Equiv.swap 2 3)

/-- One bit exchanges the sectors and flag, another exchanges the two
levels within each sector. The spectator is fixed. -/
def permuteLevel (s t : Fin 2) : Equiv.Perm (Fin 5) :=
  (if s = 0 then .refl _ else exchangeSectors).trans
    (if t = 0 then .refl _ else exchangePairs)

def permuteFlag (s : Fin 2) : Equiv.Perm (Fin 2) :=
  if s = 0 then .refl _ else Equiv.swap 0 1

/-- This is the flag Kraus operator before averaging diagonal phases. -/
noncomputable def permutedKraus (c t d b : ℝ) (s v j : Fin 2) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  (tiltedKraus c t d b ((permuteFlag s).symm j)).submatrix (permuteLevel s v) (permuteLevel s v)

/-- The active coherent coordinates are the flag's pair and the spectator. -/
def activeLevel (j : Fin 2) : Fin 3 → Fin 5 :=
  if j = 0 then ![0, 1, 4] else ![2, 3, 4]

theorem diagonal_zero_outside_active (c t d b : ℝ) (s v j : Fin 2) (i : Fin 5)
    (hi : i ∉ Set.range (activeLevel j)) : permutedKraus c t d b s v j i i = 0 := by
  fin_cases s <;> fin_cases v <;> fin_cases j <;> fin_cases i <;>
    simp [permutedKraus, permuteFlag, permuteLevel, exchangeSectors, exchangePairs,
      firstKraus, secondKraus, Equiv.swap_apply_def, activeLevel] at *
  all_goals
    first
    | exact hi ⟨0, rfl⟩
    | exact hi ⟨1, rfl⟩
    | exact hi ⟨2, rfl⟩

/-- The four equiprobable relabelings give exactly two copies of the first
branch and one copy of each ordering of the second branch on either flag. -/
theorem averaged_coherent_block (c t d b : ℝ) (j : Fin 2) :
    (1 / 4 : ℝ) • (∑ s : Fin 2, ∑ v : Fin 2,
      let z : Fin 3 → ℂ := fun i =>
        permutedKraus c t d b s v j (activeLevel j i) (activeLevel j i)
      vecMulVec z (star z)) =
    averagedCoherentGram c (d * c) (b * t) := by
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [Fin.sum_univ_two, permutedKraus, permuteFlag, permuteLevel,
      exchangeSectors, exchangePairs, firstKraus, secondKraus,
      Equiv.swap_apply_def, activeLevel, averagedCoherentGram, vecMulVec, Pi.star_apply,
      Matrix.smul_apply, Matrix.add_apply] <;> ring

end D5.S3.Quantum.Measurement.Auric.TiltedPermutationGram
