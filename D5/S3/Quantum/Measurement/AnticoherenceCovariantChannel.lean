/- GID: D5/S3/Quantum/Measurement/AnticoherenceCovariantChannel
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceCovariantChannel
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sparse spin-four Kraus operators preserve trace and evaluate the witness state. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Measurement.AnticoherenceCovariantChannel

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)

def witnessState : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r => (![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℂ) / 1764)

def witnessKraus : Fin 5 → Matrix (Fin 9) (Fin 9) ℂ :=
  ![(1 / (Real.sqrt 1540 : ℂ)) • ((3 : ℂ) • (Jz 8 * Jz 8) - (20 : ℂ) • 1),
    (-(Real.sqrt (3 / 3080) : ℂ)) • (Jz 8 * Jplus 8 + Jplus 8 * Jz 8),
    (Real.sqrt (3 / 3080) : ℂ) • (Jz 8 * (Jplus 8)ᴴ + (Jplus 8)ᴴ * Jz 8),
    (Real.sqrt (3 / 3080) : ℂ) • (Jplus 8 * Jplus 8),
    (Real.sqrt (3 / 3080) : ℂ) • ((Jplus 8)ᴴ * (Jplus 8)ᴴ)]

def witnessChannel : MatrixMap (Fin 9) (Fin 9) ℂ :=
  MatrixMap.of_kraus witnessKraus witnessKraus

def quadrupole (a b : Fin 3) : Matrix (Fin 9) (Fin 9) ℂ :=
  let j : Fin 3 → Matrix (Fin 9) (Fin 9) ℂ := ![Jx 8, Jy 8, Jz 8]
  (1 / 2 : ℂ) • (j a * j b + j b * j a) -
    (if a = b then (20 / 3 : ℂ) else 0) • 1

def witnessOutput : Matrix (Fin 9) (Fin 9) ℂ :=
  diagonal (fun r =>
    (![22288, 30100, 25528, 13149, 45540, 10584, 24654, 11613, 10584] r : ℂ) / 194040)


private def krausShift : Fin 5 → ℤ := ![0, -1, 1, -2, 2]

private def krausAmplitude (q : Fin 5) (r : Fin 9) : ℝ :=
  let z : ℝ := 4 - r.val
  let c := Real.sqrt (3 / 3080)
  ![(3 * z ^ 2 - 20) / Real.sqrt 1540,
    -c * (2 * z + 1) * Real.sqrt (20 - z * (z + 1)),
    c * (2 * z - 1) * Real.sqrt (20 - (z - 1) * z),
    c * Real.sqrt (20 - z * (z + 1)) * Real.sqrt (20 - (z + 1) * (z + 2)),
    c * Real.sqrt (20 - (z - 1) * z) * Real.sqrt (20 - (z - 2) * (z - 1))] q

private def krausWeight (q : Fin 5) (r : Fin 9) : ℝ :=
  let z : ℝ := 4 - r.val
  ![(3 * z ^ 2 - 20) ^ 2 / 1540,
    3 / 3080 * (2 * z + 1) ^ 2 * (20 - z * (z + 1)),
    3 / 3080 * (2 * z - 1) ^ 2 * (20 - (z - 1) * z),
    3 / 3080 * (20 - z * (z + 1)) * (20 - (z + 1) * (z + 2)),
    3 / 3080 * (20 - (z - 1) * z) * (20 - (z - 2) * (z - 1))] q

set_option maxHeartbeats 4000000 in
-- The five sparse matrices have nine input and output indices.
private lemma kraus_entry (q : Fin 5) (i r : Fin 9) :
    witnessKraus q i r =
      if (i.val : ℤ) = (r.val : ℤ) + krausShift q then (krausAmplitude q r : ℂ)
      else 0 := by
  rw [witnessKraus, krausShift, krausAmplitude]
  fin_cases q <;> fin_cases i <;> fin_cases r <;>
    norm_num [witnessKraus, krausShift, krausAmplitude, Jplus, Jz, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_ofReal] <;> ring

private lemma kraus_amplitude_sq (q : Fin 5) (r : Fin 9) :
    krausAmplitude q r ^ 2 = krausWeight q r := by
  rw [krausWeight]
  fin_cases q <;> fin_cases r <;>
    norm_num [krausAmplitude, krausWeight, mul_pow, div_pow, Real.sq_sqrt]

private lemma kraus_column_product (q : Fin 5) (i : Fin 9) (r s : Fin 9) :
    star (witnessKraus q i r) * witnessKraus q i s =
      if r = s ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q then
        (krausWeight q r : ℂ) else 0 := by
  rw [kraus_entry, kraus_entry]
  by_cases hr : (i.val : ℤ) = (r.val : ℤ) + krausShift q
  · by_cases hs : (i.val : ℤ) = (s.val : ℤ) + krausShift q
    · have hrs : r = s := Fin.ext (by omega)
      subst s
      simp only [hr, ite_true, true_and, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← sq, kraus_amplitude_sq]
    · have hrs : r ≠ s := by intro he; subst s; exact hs hr
      have hnot : ¬ (r = s ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q) :=
        fun h => hrs h.1
      rw [if_pos hr, if_neg hs, if_neg hnot, mul_zero]
  · simp [hr]

theorem kraus_complete : ∑ q, (witnessKraus q)ᴴ * witnessKraus q = 1 := by
  ext r s
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [kraus_column_product]
  fin_cases r <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ, krausShift, krausWeight, Matrix.one_apply]


theorem witness_state : witnessState.PosSemidef ∧ witnessState.trace = 1 := by
  rw [witnessState]
  constructor
  · apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]
  · norm_num [witnessState, trace_diagonal, Fin.sum_univ_succ]

private lemma kraus_row_product (q : Fin 5) (i j r : Fin 9) :
    witnessKraus q i r * star (witnessKraus q j r) =
      if i = j ∧ (i.val : ℤ) = (r.val : ℤ) + krausShift q then
        (krausWeight q r : ℂ) else 0 := by
  rw [kraus_entry, kraus_entry]
  by_cases hi : (i.val : ℤ) = (r.val : ℤ) + krausShift q
  · by_cases hj : (j.val : ℤ) = (r.val : ℤ) + krausShift q
    · have hij : i = j := Fin.ext (by omega)
      subst j
      simp only [hi, ite_true, true_and, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← sq, kraus_amplitude_sq]
    · have hij : i ≠ j := by intro he; subst j; exact hj hi
      simp [hi, hj, hij]
  · simp [hi]

private lemma channel_diagonal_entry (p : Fin 9 → ℂ) (i j : Fin 9) :
    witnessChannel (diagonal p) i j = ∑ q : Fin 5, ∑ r : Fin 9,
      p r * (witnessKraus q i r * star (witnessKraus q j r)) := by
  rw [witnessChannel]
  simp only [witnessChannel, MatrixMap.of_kraus, LinearMap.coe_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro r _
  ring

set_option maxHeartbeats 1000000 in
-- Nine diagonal entries each sum the five Kraus contributions.
theorem witness_output : witnessChannel witnessState = witnessOutput := by
  rw [witnessOutput]
  ext i j
  change witnessChannel (diagonal (fun r =>
    (![209, 92, 560, 0, 441, 0, 294, 168, 0] r : ℂ) / 1764)) i j = witnessOutput i j
  rw [channel_diagonal_entry]
  simp_rw [kraus_row_product]
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      norm_num [Fin.sum_univ_succ, krausShift, krausWeight, witnessOutput]
  · simp [hij, witnessOutput]


end D5.S3.Quantum.Measurement.AnticoherenceCovariantChannel
