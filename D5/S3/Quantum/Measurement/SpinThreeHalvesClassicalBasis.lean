/- GID: D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Spin-3/2 orthonormal bases have mean one-qubit anticoherence at least one ninth. -/

import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound

/-! The normalized Dicke reduction and the sharp spin-3/2 basis anticoherence bound. -/

noncomputable section
open scoped BigOperators Matrix
open Matrix Complex

namespace D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis

/-- The normalized three-qubit Dicke embedding, with the number of ones as spin index. -/
def dicke (ψ : Fin 4 → ℂ) (x : Fin 2 × Fin 2 × Fin 2) : ℂ :=
  ψ ⟨x.1.val + x.2.1.val + x.2.2.val, by omega⟩ /
    (Real.sqrt (Nat.choose 3 (x.1.val + x.2.1.val + x.2.2.val) : ℝ) : ℂ)

/-- Trace over the first two qubits. -/
def reducedState (ψ : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun c d => ∑ a : Fin 2, ∑ b : Fin 2,
    dicke ψ (a, b, c) * star (dicke ψ (a, b, d))

def anticoherence (ψ : Fin 4 → ℂ) : ℝ :=
  2 * (1 - (reducedState ψ * reducedState ψ).trace.re)

def basisAnticoherence (U : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  (1 / 4) * ∑ i, anticoherence (fun k => U k i)

/-- The matrix in Eq. (21), with the algebraic expression for the cube root of unity. -/
def classicalBasis : Matrix (Fin 4) (Fin 4) ℂ :=
  let ν : ℂ := (Real.sqrt 3 : ℂ) * (2 - (Real.sqrt 2 : ℂ))
  let τ : ℂ := 3 - 2 * (Real.sqrt 2 : ℂ)
  let ω : ℂ := (-1 + I * (Real.sqrt 3 : ℂ)) / 2
  (1 / (Real.sqrt (18 * (3 - 2 * Real.sqrt 2)) : ℂ)) •
    !![1, 1, 1, τ * (Real.sqrt 3 : ℂ);
       ν, ν * ω, ν * ω ^ 2, 0;
       ν, ν * ω ^ 2, ν * ω, 0;
       τ, τ, τ, -(Real.sqrt 3 : ℂ)]

def claim : Prop :=
  (∀ U ∈ Matrix.unitaryGroup (Fin 4) ℂ, 1 / 9 ≤ basisAnticoherence U) ∧
    classicalBasis ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    basisAnticoherence classicalBasis = 1 / 9

private def polarization (ψ : Fin 4 → ℂ) : Fin 3 → ℝ :=
  ![(star ψ ⬝ᵥ
      (D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jx 3 *ᵥ ψ)).re,
    (star ψ ⬝ᵥ
      (D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy 3 *ᵥ ψ)).re,
    (star ψ ⬝ᵥ
      (D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jz 3 *ᵥ ψ)).re]

private lemma reduced_entries (ψ : Fin 4 → ℂ) :
    reducedState ψ =
      !![ψ 0 * star (ψ 0) + (2 * (ψ 1 * star (ψ 1)) + ψ 2 * star (ψ 2)) / 3,
         (Real.sqrt 3 : ℂ) / 3 * (ψ 0 * star (ψ 1) + ψ 2 * star (ψ 3)) +
           2 / 3 * (ψ 1 * star (ψ 2));
         (Real.sqrt 3 : ℂ) / 3 * (ψ 1 * star (ψ 0) + ψ 3 * star (ψ 2)) +
           2 / 3 * (ψ 2 * star (ψ 1)),
         ψ 3 * star (ψ 3) + (ψ 1 * star (ψ 1) + 2 * (ψ 2 * star (ψ 2))) / 3] := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 3 : ℂ) ≠ 0 := by norm_cast; positivity
  have hi : (Real.sqrt 3 : ℂ)⁻¹ = (Real.sqrt 3 : ℂ) / 3 := by
    field_simp
    linear_combination -hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reducedState, dicke, Fin.sum_univ_two, Nat.choose,
      map_div₀, Complex.conj_ofReal, Complex.star_def, div_eq_mul_inv, hi] <;>
    ring_nf <;> simp [hs] <;> ring

private lemma polarization_entries (ψ : Fin 4 → ℂ) :
    polarization ψ =
      ![((Real.sqrt 3 : ℂ) * (star (ψ 0) * ψ 1 + star (ψ 2) * ψ 3) +
          2 * (star (ψ 1) * ψ 2)).re,
        ((Real.sqrt 3 : ℂ) * (star (ψ 0) * ψ 1 + star (ψ 2) * ψ 3) +
          2 * (star (ψ 1) * ψ 2)).im,
        (3 * Complex.normSq (ψ 0) + Complex.normSq (ψ 1) -
          Complex.normSq (ψ 2) - 3 * Complex.normSq (ψ 3)) / 2] := by
  have h4 : Real.sqrt 4 = 2 := by
    exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num)
  ext a
  fin_cases a <;>
    norm_num [polarization, h4,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jx,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jz,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jplus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.normSq] <;> ring

private lemma dicke_bridge (ψ : Fin 4 → ℂ)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    anticoherence ψ = 1 - 4 / 9 * ∑ a, (polarization ψ a) ^ 2 := by
  have hnorm : (∑ i, Complex.normSq (ψ i)) ^ 2 = 1 := by rw [hψ]; norm_num
  simp only [Fin.sum_univ_four, Complex.normSq_apply] at hnorm
  rw [anticoherence, reduced_entries, polarization_entries]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.normSq]
  linear_combination (norm := ring_nf) -hnorm

private lemma classical_entries :
    classicalBasis =
      !![(((2 + Real.sqrt 2) / 6 : ℝ) : ℂ), (((2 + Real.sqrt 2) / 6 : ℝ) : ℂ),
           (((2 + Real.sqrt 2) / 6 : ℝ) : ℂ), ((Real.sqrt 3 * (2 - Real.sqrt 2) / 6 : ℝ) : ℂ);
         ((Real.sqrt 3 / 3 : ℝ) : ℂ), ⟨-Real.sqrt 3 / 6, 1 / 2⟩,
           ⟨-Real.sqrt 3 / 6, -1 / 2⟩, 0;
         ((Real.sqrt 3 / 3 : ℝ) : ℂ), ⟨-Real.sqrt 3 / 6, -1 / 2⟩,
           ⟨-Real.sqrt 3 / 6, 1 / 2⟩, 0;
         (((2 - Real.sqrt 2) / 6 : ℝ) : ℂ), (((2 - Real.sqrt 2) / 6 : ℝ) : ℂ),
           (((2 - Real.sqrt 2) / 6 : ℝ) : ℂ),
           ((-Real.sqrt 3 * (2 + Real.sqrt 2) / 6 : ℝ) : ℂ)] := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h33 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    linear_combination Real.sqrt 3 * h3
  have hpos : 0 < 6 - 3 * Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2
    nlinarith
  have hd : Real.sqrt (18 * (3 - 2 * Real.sqrt 2)) = 6 - 3 * Real.sqrt 2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos hpos).mpr
    nlinarith
  have hi : (6 - 3 * Real.sqrt 2)⁻¹ = (2 + Real.sqrt 2) / 6 := by
    field_simp
    nlinarith
  have his : (1 / (Real.sqrt (18 * (3 - 2 * Real.sqrt 2)) : ℂ)) =
      (((2 + Real.sqrt 2) / 6 : ℝ) : ℂ) := by
    rw [one_div, ← Complex.ofReal_inv, hd, hi]
  unfold classicalBasis
  rw [his]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [ Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq] <;>
    ring_nf <;>
    norm_num [map_ofNat, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq, h2, h3, h33] <;>
    ring_nf <;> norm_num [pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [h2, h3, h33] <;> ring

private lemma classical_unitary : classicalBasis ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, classical_entries]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;>
    norm_num [map_ofNat, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq, h2, h3] <;>
    ring_nf <;> norm_num [h2, h3] <;> ring

private lemma classical_polarization (i : Fin 4) :
    polarization (fun k => classicalBasis k i) =
      ![![4 / 3, 0, Real.sqrt 2 / 3],
        ![-2 / 3, 2 * Real.sqrt 3 / 3, Real.sqrt 2 / 3],
        ![-2 / 3, -2 * Real.sqrt 3 / 3, Real.sqrt 2 / 3],
        ![0, 0, -Real.sqrt 2]] i := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [polarization_entries, classical_entries]
  ext a
  fin_cases i <;> fin_cases a <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;>
    ring_nf <;>
    norm_num [map_ofNat, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq, h2, h3] <;>
    ring_nf <;> norm_num [h2, h3]

private lemma classical_attainment : basisAnticoherence classicalBasis = 1 / 9 := by
  have hu := Matrix.mem_unitaryGroup_iff'.mp classical_unitary
  have hc (i : Fin 4) : ∑ k, Complex.normSq (classicalBasis k i) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M i i).re) hu
    simpa [Matrix.mul_apply, Complex.mul_re, Complex.normSq_apply] using h
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold basisAnticoherence
  simp_rw [dicke_bridge _ (hc _), classical_polarization]
  norm_num [Fin.sum_univ_succ, div_pow, mul_pow, h2, h3]

private lemma universal_bound (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) : 1 / 9 ≤ basisAnticoherence U := by
  sorry

theorem result : claim :=
  ⟨universal_bound, classical_unitary, classical_attainment⟩

end D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
