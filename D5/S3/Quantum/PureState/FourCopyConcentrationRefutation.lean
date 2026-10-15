/- GID: D5/S3/Quantum/PureState/FourCopyConcentrationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/FourCopyConcentrationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.claim; result=D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result; claim=D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.claim
   digest: A singlet-sector protocol refutes the direct four-copy concentration bound. -/

import D5.S3.Quantum.QubitWitnesses
import D5.S3.Quantum.Entanglement.QutritThresholdSharing
import D5.S3.QuantumBounds.StatisticalStrengthMagicSquare

set_option linter.style.longLine false

open scoped BigOperators Matrix ComplexOrder ComplexConjugate
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.QubitWitnesses (bellCoefficients)
open D5.S3.QuantumBounds.StatisticalStrengthMagicSquare (rationalSinglets)

namespace D5.S3.Quantum.PureState.FourCopyConcentrationRefutation

noncomputable section

/-- Four local qubits, ordered as the two pairs `(1, 2)` and `(3, 4)`. -/
abbrev Q := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The normalization of the two-qubit pure-state coefficient matrix. -/
def normalized (C : QubitMatrix) : Prop :=
  (∑ i : Fin 2, ∑ j : Fin 2, ‖C i j‖ ^ 2) = 1

/-- Four-copy coefficients with Alice's four bits against Bob's four bits. -/
def amp4 (C : QubitMatrix) (a b : Q) : ℂ :=
  C a.1.1 b.1.1 * C a.1.2 b.1.2 * C a.2.1 b.2.1 * C a.2.2 b.2.2

/-- Local success operators act on coefficients with Bob's factor transposed. -/
def output (KA KB : Matrix (Fin 2) Q ℂ) (C : QubitMatrix) : QubitMatrix :=
  fun i j => ∑ a : Q, ∑ b : Q, KA i a * KB j b * amp4 C a b

/-- Every normalized input produces a scalar multiple of the Bell vector, including zero. -/
def universal (KA KB : Matrix (Fin 2) Q ℂ) : Prop :=
  ∀ C : QubitMatrix, normalized C →
    output KA KB C 0 1 = 0 ∧ output KA KB C 1 0 = 0 ∧
      output KA KB C 0 0 = output KA KB C 1 1

/-- The squared norm of the unnormalized success output. -/
def success (KA KB : Matrix (Fin 2) Q ℂ) (C : QubitMatrix) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ‖output KA KB C i j‖ ^ 2

/-- The literal four-copy bound of Eq. (8). -/
def B (C : QubitMatrix) : ℝ :=
  2 * ‖C 0 1 ^ 4 * C 1 0 ^ 4‖ + 2 * ‖C 0 0 ^ 4 * C 1 1 ^ 4‖ -
    4 * (C 0 0 ^ 2 * C 1 1 ^ 2 * (conj (C 0 1)) ^ 2 * (conj (C 1 0)) ^ 2).re

/-- The direct four-copy bound restricted to locally contractive product success operators. -/
def claim : Prop :=
  ∀ KA KB : Matrix (Fin 2) Q ℂ, (1 - KAᴴ * KA).PosSemidef →
    (1 - KBᴴ * KB).PosSemidef → universal KA KB →
      ∀ C, normalized C → success KA KB C ≤ B C

/-- The product of singlets on positions `(1, 2)` and `(3, 4)`. -/
def u (q : Q) : ℂ :=
  rationalSinglets ((q.1.1, q.2.1), (q.1.2, q.2.2))

/-- The orthogonal second singlet-sector vector. -/
def v (q : Q) : ℂ := (Real.sqrt 3 : ℂ)⁻¹ * (2 * rationalSinglets q - u q)

/-- The two real singlet-sector bras form the local success operator. -/
def K : Matrix (Fin 2) Q ℂ := fun i q => if i = 0 then u q else v q

/-- A normalized maximally entangled input whose Eq. (8) bound is zero. -/
def C0 : QubitMatrix := !![(1 / 2 : ℂ), 1 / 2; -1 / 2, 1 / 2]

/-- The singlet-sector success output is the determinant square times the Bell array. -/
private theorem output_K (C : QubitMatrix) :
    output K K C = C.det ^ 2 • bellCoefficients := by
  have hpoly : output K K C =
      !![C.det ^ 2, 0; 0, 3 * ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 * C.det ^ 2] := by
    funext i j
    simp only [output.eq_1, K.eq_1, v.eq_1, ← Complex.ofReal_inv]
    generalize (Real.sqrt (3 : ℝ))⁻¹ = t
    fin_cases i <;> fin_cases j <;>
      norm_num [amp4.eq_1, u.eq_1, rationalSinglets, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.det_fin_two] <;> ring
  have hn : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = (1 / 3 : ℂ) := by
    simpa only [pow_two, one_div] using
      D5.S3.Quantum.Entanglement.QutritThresholdSharing.normalization
  rw [hpoly, hn]
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [bellCoefficients]

/-- The rows of the local success operator are orthonormal. -/
private theorem K_coisometry : K * Kᴴ = (1 : QubitMatrix) := by
  have hpoly : K * Kᴴ = !![1, 0; 0, 3 * ((Real.sqrt 3 : ℂ)⁻¹) ^ 2] := by
    funext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K.eq_1, v.eq_1,
      ← Complex.ofReal_inv]
    generalize (Real.sqrt (3 : ℝ))⁻¹ = t
    fin_cases i <;> fin_cases j <;>
      norm_num [u.eq_1, rationalSinglets, Fintype.sum_prod_type, Fin.sum_univ_two,
        Complex.star_def, map_ofNat]
    all_goals ring
  have hn : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = (1 / 3 : ℂ) := by
    simpa only [pow_two, one_div] using
      D5.S3.Quantum.Entanglement.QutritThresholdSharing.normalization
  rw [hpoly, hn]
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The local success operator completes to a quantum instrument. -/
private theorem K_contraction : (1 - Kᴴ * K).PosSemidef := by
  have hp : (Kᴴ * K) * (Kᴴ * K) = Kᴴ * K := by
    calc
      (Kᴴ * K) * (Kᴴ * K) = Kᴴ * (K * Kᴴ) * K := by
        simp only [Matrix.mul_assoc]
      _ = Kᴴ * K := by rw [K_coisometry]; simp
  have he : (1 - Kᴴ * K)ᴴ * (1 - Kᴴ * K) = 1 - Kᴴ * K := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (1 - Kᴴ * K) * (1 - Kᴴ * K) =
          1 - Kᴴ * K - Kᴴ * K + (Kᴴ * K) * (Kᴴ * K) := by noncomm_ring
      _ = 1 - Kᴴ * K := by rw [hp]; abel
  have hpos := Matrix.posSemidef_conjTranspose_mul_self (1 - Kᴴ * K)
  rw [he] at hpos
  exact hpos

/-- The same fixed local instrument is conclusive for every normalized pure input. -/
private theorem K_universal : universal K K := by
  rw [universal.eq_1]
  intro C _
  simp [output_K, bellCoefficients]

private theorem C0_normalized : normalized C0 := by
  norm_num [normalized.eq_1, C0.eq_1, Fin.sum_univ_two, norm_div]

private theorem C0_det : C0.det = (1 / 2 : ℂ) := by
  norm_num [C0.eq_1, Matrix.det_fin_two]

private theorem success_C0 : success K K C0 = (1 / 8 : ℝ) := by
  norm_num [success.eq_1, output_K, C0_det, bellCoefficients, Fin.sum_univ_two, norm_div]

private theorem B_C0 : B C0 = 0 := by
  norm_num [B.eq_1, C0.eq_1, norm_mul, norm_pow, norm_div, map_ofNat]

/-- A universal direct four-copy singlet-sector protocol exceeds the proposed bound. -/
theorem result : ¬ claim := by
  intro h
  rw [claim.eq_1] at h
  have hbad := h K K K_contraction K_contraction K_universal C0 C0_normalized
  rw [success_C0, B_C0] at hbad
  norm_num at hbad

end

end D5.S3.Quantum.PureState.FourCopyConcentrationRefutation
