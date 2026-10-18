/- GID: D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Spin-3/2 orthonormal bases have mean one-qubit anticoherence at least one ninth. -/

import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import D5.S3.Quantum.Matrix.WeightedBotcherWenzel
import D5.S3.Quantum.Schatten.CompoundMatrices

/-! The normalized Dicke reduction and the sharp spin-3/2 basis anticoherence bound. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
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
           (((2 + Real.sqrt 2) / 6 : ℝ) : ℂ),
           ((Real.sqrt 3 * (2 - Real.sqrt 2) / 6 : ℝ) : ℂ);
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
    ring_nf

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
  fin_cases i <;> fin_cases a
  all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  all_goals ring_nf
  all_goals norm_num [map_ofNat, Complex.mul_re, Complex.mul_im, Complex.inv_re,
    Complex.inv_im, Complex.normSq, h2, h3]
  all_goals ring_nf

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

private lemma phase_invariance (ψ : Fin 4 → ℂ) (z : ℂ) (hz : star z * z = 1) :
    anticoherence (fun i => z * ψ i) = anticoherence ψ := by
  have hr : reducedState (fun i => z * ψ i) = reducedState ψ := by
    ext c d
    simp only [reducedState.eq_1]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [dicke.eq_1, star_div₀, star_mul]
    calc
      _ = (star z * z) *
          (ψ ⟨a.val + b.val + c.val, by omega⟩ /
              (Real.sqrt (Nat.choose 3 (a.val + b.val + c.val) : ℝ) : ℂ) *
            (star (ψ ⟨a.val + b.val + d.val, by omega⟩) /
              star (Real.sqrt (Nat.choose 3 (a.val + b.val + d.val) : ℝ) : ℂ))) := by
            ring
      _ = _ := by rw [hz, one_mul]
  simp only [anticoherence, hr]

set_option maxHeartbeats 800000 in
-- The finite column computations share a determinant phase.
private lemma phase_reduction (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 4) ℂ,
      V.det = 1 ∧ basisAnticoherence V = basisAnticoherence U := by
  let z : ℂ := U.det⁻¹
  have hd := Matrix.det_of_mem_unitary hU
  have hz : star z * z = 1 := by
    dsimp [z]
    rw [map_inv₀, ← _root_.mul_inv_rev]
    change (U.det * star U.det)⁻¹ = 1
    rw [hd.2, inv_one]
  let D : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![z, 1, 1, 1]
  have hD : D ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, Matrix.mul_apply, Fin.sum_univ_succ]
    exact hz
  refine ⟨U * D, mul_mem hU hD, ?_, ?_⟩
  · rw [Matrix.det_mul]
    simp [D, Matrix.det_diagonal, Fin.prod_univ_succ, z,
      show U.det ≠ 0 from (Matrix.UnitaryGroup.det_isUnit ⟨U, hU⟩).ne_zero]
  · unfold basisAnticoherence
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    fin_cases i
    · simpa [D, Matrix.mul_diagonal, mul_comm] using
        phase_invariance (fun k => U k 0) z hz
    all_goals simp [D, Matrix.mul_diagonal]

private def pair (i : Fin 6) : Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] i

private def pairSet (i : Fin 6) : {S : Finset (Fin 4) // S.card = 2} :=
  ⟨{(pair i).1, (pair i).2}, by fin_cases i <;> decide⟩

private lemma pairSet_bijective : Function.Bijective pairSet := by decide

private def compound (U : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => U (pair i).1 (pair j).1 * U (pair i).2 (pair j).2 -
    U (pair i).1 (pair j).2 * U (pair i).2 (pair j).1

private lemma compound_mul (U V : Matrix (Fin 4) (Fin 4) ℂ) :
    compound (U * V) = compound U * compound V := by
  have he (i : Fin 6) :
      (pairSet i).1.orderEmbOfFin (pairSet i).2 = ![(pair i).1, (pair i).2] := by
    have hs : (pairSet i).1.sort (· ≤ ·) = [(pair i).1, (pair i).2] := by
      change Finset.sort ({(pair i).1, (pair i).2} : Finset (Fin 4)) (· ≤ ·) = _
      rw [Finset.sort_insert (· ≤ ·) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide), Finset.sort_singleton]
    funext k
    simp only [Finset.orderEmbOfFin_apply, hs]
    fin_cases k <;> rfl
  ext i j
  have h := cauchyBinet (U.submatrix ![(pair i).1, (pair i).2] id)
    (V.submatrix id ![(pair j).1, (pair j).2])
  rw [← pairSet_bijective.sum_comp] at h
  simp only [he, Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, id_eq] at h
  simpa only [compound, Matrix.mul_apply, Fin.sum_univ_two, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, id_eq] using h

private lemma compound_star (U : Matrix (Fin 4) (Fin 4) ℂ) :
    compound Uᴴ = (compound U)ᴴ := by
  ext i j
  simp only [compound.eq_1, Matrix.conjTranspose_apply, star_sub, star_mul]
  ring

private lemma compound_one : compound (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [compound, pair, Matrix.one_apply]

private lemma compound_unitary (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    compound U ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ← compound_star, ← compound_mul,
    show Uᴴ * U = 1 from Matrix.mem_unitaryGroup_iff'.mp hU, compound_one]

private def complementForm : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

set_option maxHeartbeats 1800000 in
-- The six-pair determinant expansion is a finite polynomial calculation.
private lemma compound_pairing (U : Matrix (Fin 4) (Fin 4) ℂ) :
    (compound U)ᵀ * complementForm * compound U = U.det • complementForm := by
  have hd : U.det =
      ∑ j : Fin 4, (-1 : ℂ) ^ j.val * U 0 j *
        (U.submatrix (Fin.succ) (j.succAbove)).det := Matrix.det_succ_row_zero U
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, compound, pair, complementForm,
      Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove] <;> ring

private def realBasis : Matrix (Fin 6) (Fin 6) ℂ :=
  ((Real.sqrt 2 : ℂ) / 2) •
    !![1, I, 0, 0, 0, 0;
       0, 0, 1, I, 0, 0;
       0, 0, 0, 0, 1, I;
       0, 0, 0, 0, 1, -I;
       0, 0, -1, I, 0, 0;
       1, -I, 0, 0, 0, 0]

set_option maxHeartbeats 1800000 in
-- The three identities each evaluate all entries of a six-dimensional matrix.
private lemma realBasis_identities :
    realBasisᴴ * realBasis = 1 ∧
    realBasisᵀ * complementForm * realBasis = 1 ∧
    (realBasisᴴ)ᵀ * realBasisᴴ = complementForm := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [complementForm.eq_1]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;>
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [realBasis, complementForm, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> ring_nf <;> simp [hs] <;>
    ring_nf <;> norm_num [hs]

private def transported (U : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  realBasisᴴ * compound U * realBasis

private lemma transported_real_orthogonal (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (hdet : U.det = 1) :
    (∀ i j, (transported U i j).im = 0) ∧
      (transported U)ᵀ * transported U = 1 := by
  obtain ⟨hB, hC, hD⟩ := realBasis_identities
  have hW := compound_unitary U hU
  have hQ : transported U ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
    apply mul_mem
    · exact mul_mem (Unitary.star_mem (show realBasis ∈ Matrix.unitaryGroup (Fin 6) ℂ from
        Matrix.mem_unitaryGroup_iff'.mpr hB)) hW
    · exact Matrix.mem_unitaryGroup_iff'.mpr hB
  have horth : (transported U)ᵀ * transported U = 1 := by
    calc
      _ = realBasisᵀ * (compound U)ᵀ * ((realBasisᴴ)ᵀ * realBasisᴴ) *
          compound U * realBasis := by
        simp only [transported, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = realBasisᵀ * ((compound U)ᵀ * complementForm * compound U) * realBasis := by
        rw [hD]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [compound_pairing, hdet, one_smul, hC]
  have he : (transported U)ᵀ = (transported U)ᴴ := by
    calc
      _ = (transported U)ᵀ * (transported U * (transported U)ᴴ) := by
        rw [show transported U * (transported U)ᴴ = 1 from hQ.2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, horth, Matrix.one_mul]
  refine ⟨?_, horth⟩
  intro i j
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => (M j i).im) he
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_im] at h
  linarith

private lemma unweighted_bw (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    RHLinalg.frobSq (A * B - B * A) ≤ 2 * RHLinalg.frobSq A * RHLinalg.frobSq B := by
  have he (i : Fin 3) :
      (isHermitian_one : (1 : Matrix (Fin 3) (Fin 3) ℂ).IsHermitian).eigenvalues i = 1 := by
    have h := Matrix.IsHermitian.eigenvalues_mem_spectrum_real
      (isHermitian_one : (1 : Matrix (Fin 3) (Fin 3) ℂ).IsHermitian) i
    simpa [spectrum.one_eq] using h
  have hs : D5.S3.Quantum.Matrix.WeightedBotcherWenzel.SpectralExtrema
      (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 1 :=
    ⟨isHermitian_one, fun i => by simp [he], ⟨0, he 0⟩, ⟨0, he 0⟩⟩
  have h := D5.S3.Quantum.Matrix.WeightedBotcherWenzel.result 3 (by norm_num)
    1 1 1 Matrix.PosDef.one (by norm_num) hs A B
  simpa [D5.S3.Quantum.Matrix.WeightedBotcherWenzel.weighted_one,
    D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator,
    show (1 : ℝ) + 1 = 2 by norm_num] using h

private lemma refined_bw (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    RHLinalg.frobSq (A * B - B * A) ≤
      2 * (RHLinalg.frobSq A * RHLinalg.frobSq B - (Aᴴ * B).trace.re ^ 2) := by
  let a := RHLinalg.frobSq A
  let c := (Aᴴ * B).trace.re
  by_cases hz : a = 0
  · have hc := D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy Aᴴ B
    rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_star] at hc
    have hb := unweighted_bw A B
    change Complex.normSq (Aᴴ * B).trace ≤ a * RHLinalg.frobSq B at hc
    change RHLinalg.frobSq (A * B - B * A) ≤ 2 * a * RHLinalg.frobSq B at hb
    simp only [hz, zero_mul] at hc hb
    have hc0 : c = 0 := by
      dsimp [c]
      simp only [Complex.normSq_apply] at hc
      nlinarith [sq_nonneg (Aᴴ * B).trace.re, sq_nonneg (Aᴴ * B).trace.im]
    change RHLinalg.frobSq (A * B - B * A) ≤ 2 * (a * _ - c ^ 2)
    simpa [hz, hc0] using hb
  · let t := c / a
    have hshift : RHLinalg.frobSq (B - (t : ℂ) • A) =
        RHLinalg.frobSq B - 2 * t * c + t ^ 2 * a := by
      simp [RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, a, c]
      ring
    have hcomm : A * (B - (t : ℂ) • A) - (B - (t : ℂ) • A) * A =
        A * B - B * A := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      abel
    have hb := unweighted_bw A (B - (t : ℂ) • A)
    rw [hcomm, hshift] at hb
    have he : 2 * a * (RHLinalg.frobSq B - 2 * t * c + t ^ 2 * a) =
        2 * (a * RHLinalg.frobSq B - c ^ 2) := by
      dsimp [t]
      field_simp
      ring
    change RHLinalg.frobSq (A * B - B * A) ≤ 2 * a * _ at hb
    rw [he] at hb
    exact hb

private def evenIndex : Fin 3 → Fin 6 := ![0, 2, 4]
private def oddIndex : Fin 3 → Fin 6 := ![1, 3, 5]

private def shape (v : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := Real.sqrt 2 / 2
  let b := Real.sqrt 2 * Real.sqrt 3 / 6
  !![(a * v 0 - b * v 4 : ℝ), (-a * v 1 : ℝ), (a * v 2 : ℝ);
     (-a * v 1 : ℝ), (-a * v 0 - b * v 4 : ℝ), (-a * v 3 : ℝ);
     (a * v 2 : ℝ), (-a * v 3 : ℝ), (2 * b * v 4 : ℝ)]

private lemma shape_pair (v w : Fin 6 → ℝ) :
    ((shape v)ᴴ * shape w).trace.re = ∑ i, v i * w i - v 5 * w 5 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num [shape, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.inv_re,
    Complex.inv_im, Complex.normSq, pow_two]
  ring_nf
  norm_num [h2, h3]
  ring_nf
  norm_num [h2, h3]
  ring

private lemma frame_bound (O : Matrix (Fin 6) (Fin 6) ℝ) (hO : Oᵀ * O = 1) :
    2 * ∑ k : Fin 3,
      RHLinalg.frobSq
        (shape (fun i => O i (evenIndex k)) * shape (fun i => O i (oddIndex k)) -
          shape (fun i => O i (oddIndex k)) * shape (fun i => O i (evenIndex k))) ≤ 8 := by
  have hdot (i j : Fin 6) : ∑ l, O l i * O l j = if i = j then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg (fun M => M i j) hO
  have hrow : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  have hs := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 5 5) hrow
  have hsum : ∑ k : Fin 3,
      (O 5 (evenIndex k) ^ 2 + O 5 (oddIndex k) ^ 2) = 1 := by
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, evenIndex, oddIndex] at hs ⊢
    nlinarith only [hs]
  have hlocal (k : Fin 3) :
      2 * RHLinalg.frobSq
        (shape (fun i => O i (evenIndex k)) * shape (fun i => O i (oddIndex k)) -
          shape (fun i => O i (oddIndex k)) * shape (fun i => O i (evenIndex k))) ≤
        4 * (1 - O 5 (evenIndex k) ^ 2 - O 5 (oddIndex k) ^ 2) := by
    have hx : RHLinalg.frobSq (shape (fun i => O i (evenIndex k))) =
        1 - O 5 (evenIndex k) ^ 2 := by
      change ((shape _)ᴴ * shape _).trace.re = _
      rw [shape_pair, hdot]
      simp [pow_two]
    have hy : RHLinalg.frobSq (shape (fun i => O i (oddIndex k))) =
        1 - O 5 (oddIndex k) ^ 2 := by
      change ((shape _)ᴴ * shape _).trace.re = _
      rw [shape_pair, hdot]
      simp [pow_two]
    have hxy : ((shape (fun i => O i (evenIndex k)))ᴴ *
        shape (fun i => O i (oddIndex k))).trace.re =
          -O 5 (evenIndex k) * O 5 (oddIndex k) := by
      rw [shape_pair, hdot]
      have hn : evenIndex k ≠ oddIndex k := by fin_cases k <;> decide
      simp [hn]
    have hb := refined_bw (shape (fun i => O i (evenIndex k)))
      (shape (fun i => O i (oddIndex k)))
    rw [hx, hy, hxy] at hb
    nlinarith only [hb]
  have ht := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hlocal k)
  norm_num [Fin.sum_univ_succ] at ht hsum ⊢
  linarith

private def spinMatrix (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jx 3,
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy 3,
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jz 3] a

private def liftSpin (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j =>
    A (pair i).1 (pair j).1 * (if (pair i).2 = (pair j).2 then 1 else 0) -
    A (pair i).1 (pair j).2 * (if (pair i).2 = (pair j).1 then 1 else 0) -
    A (pair i).2 (pair j).1 * (if (pair i).1 = (pair j).2 then 1 else 0) +
    A (pair i).2 (pair j).2 * (if (pair i).1 = (pair j).1 then 1 else 0)

private lemma one_body_expansion (U H : Matrix (Fin 4) (Fin 4) ℂ)
    (a b c d : Fin 4) :
    (∑ i : Fin 6, ∑ j : Fin 6,
      star (U (pair i).1 a * U (pair i).2 b - U (pair i).1 b * U (pair i).2 a) *
        liftSpin H i j *
        (U (pair j).1 c * U (pair j).2 d - U (pair j).1 d * U (pair j).2 c)) =
      (Uᴴ * H * U) a c * (Uᴴ * U) b d -
      (Uᴴ * H * U) a d * (Uᴴ * U) b c -
      (Uᴴ * H * U) b c * (Uᴴ * U) a d +
      (Uᴴ * H * U) b d * (Uᴴ * U) a c := by
  simp_rw [pair.eq_1]
  norm_num [liftSpin, pair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, map_sub, map_mul]
  ring

private lemma compound_one_body (U H : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    (compound U)ᴴ * liftSpin H * compound U = liftSpin (Uᴴ * H * U) := by
  ext i j
  simp only [liftSpin.eq_1]
  have h := one_body_expansion U H (pair i).1 (pair i).2 (pair j).1 (pair j).2
  rw [show Uᴴ * U = 1 from hU.1] at h
  simp only [Matrix.one_apply] at h
  change (∑ l, (∑ k, star (compound U k i) * liftSpin H k l) * compound U l j) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h

private def generator : Fin 3 → Matrix (Fin 6) (Fin 6) ℝ :=
  ![!![0, 0, 0, 1, 0, 0; 0, 0, -1, 0, 0, 0; 0, 1, 0, 0, 0, 0;
       -1, 0, 0, 0, -Real.sqrt 3, 0; 0, 0, 0, Real.sqrt 3, 0, 0;
       0, 0, 0, 0, 0, 0],
    !![0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 1, 0, 0, 0, -Real.sqrt 3, 0;
       0, 1, 0, 0, 0, 0; 0, 0, Real.sqrt 3, 0, 0, 0; 0, 0, 0, 0, 0, 0],
    !![0, 2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0;
       0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 1800000 in
-- The lifted spin operators are evaluated in the explicit six-vector basis.
private lemma generator_bridge (a : Fin 3) :
    realBasisᴴ * ((-I : ℂ) • liftSpin (spinMatrix a)) * realBasis =
      (generator a).map Complex.ofReal := by
  let r : ℂ := (Real.sqrt 3 : ℂ) / 2
  have h4 : Real.sqrt 4 = 2 := by
    exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num)
  have hL : liftSpin (spinMatrix a) =
      ![!![0, 1, 0, 0, 0, 0;
           1, 0, r, r, 0, 0;
           0, r, 0, 0, r, 0;
           0, r, 0, 0, r, 0;
           0, 0, r, r, 0, 1;
           0, 0, 0, 0, 1, 0],
        !![0, -I, 0, 0, 0, 0;
           I, 0, -I * r, -I * r, 0, 0;
           0, I * r, 0, 0, -I * r, 0;
           0, I * r, 0, 0, -I * r, 0;
           0, 0, I * r, I * r, 0, -I;
           0, 0, 0, 0, I, 0],
        !![2, 0, 0, 0, 0, 0;
           0, 1, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, 0, 0;
           0, 0, 0, 0, -1, 0;
           0, 0, 0, 0, 0, -2]] a := by
    fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [liftSpin, spinMatrix, pair, r, h4,
        D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jplus,
        D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jx,
        D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy,
        D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jz,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq] <;>
      ring
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hL, realBasis.eq_1]
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [realBasis, generator, r, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.star_def, map_ofNat,
      Complex.div_re, Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.normSq] <;>
    ring_nf <;> norm_num [h2] <;> ring

set_option maxHeartbeats 1200000 in
-- The commutator entries combine the five traceless symmetric coordinates.
private lemma commutator_coordinates (v w : Fin 6 → ℝ) :
    (∑ a : Fin 3, (v ⬝ᵥ (generator a *ᵥ w)) ^ 2) =
      2 * RHLinalg.frobSq (shape v * shape w - shape w * shape v) := by
  let g : Fin 3 → ℝ :=
    ![v 0 * w 3 - v 1 * w 2 + v 2 * w 1 - v 3 * w 0 -
        Real.sqrt 3 * v 3 * w 4 + Real.sqrt 3 * v 4 * w 3,
      -v 0 * w 2 - v 1 * w 3 + v 2 * w 0 - Real.sqrt 3 * v 2 * w 4 +
        v 3 * w 1 + Real.sqrt 3 * v 4 * w 2,
      2 * v 0 * w 1 - 2 * v 1 * w 0 + v 2 * w 3 - v 3 * w 2]
  have hg (a : Fin 3) : v ⬝ᵥ (generator a *ᵥ w) = g a := by
    rw [generator.eq_1]
    fin_cases a <;>
      norm_num [generator, g, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> ring
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : shape v * shape w - shape w * shape v =
      (!![0, -g 2 / 2, -g 1 / 2;
          g 2 / 2, 0, g 0 / 2;
          g 1 / 2, -g 0 / 2, 0]).map Complex.ofReal := by
    simp_rw [shape.eq_1]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [shape, g, Matrix.mul_apply, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.div_re, Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.normSq] <;>
      ring_nf <;> norm_num [h2, h3] <;> ring
  simp_rw [hg]
  rw [hc]
  norm_num [RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

private lemma lift_pair_entry (A : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : A.trace = 0) (k : Fin 3) :
    (realBasisᴴ * ((-I : ℂ) • liftSpin A) * realBasis) (evenIndex k) (oddIndex k) =
      A 0 0 + A k.succ k.succ := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have ht : A 0 0 + A 1 1 + A 2 2 + A 3 3 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using hA
  rw [evenIndex.eq_1, oddIndex.eq_1]
  fin_cases k <;>
    norm_num [realBasis, liftSpin, pair, Matrix.mul_apply,
      Fin.sum_univ_succ, map_ofNat] <;>
    ring_nf <;> simp [h2, Complex.I_sq] <;>
    linear_combination -ht / 2

private lemma polarization_diagonal (U : Matrix (Fin 4) (Fin 4) ℂ)
    (a : Fin 3) (i : Fin 4) :
    polarization (fun j => U j i) a = ((Uᴴ * spinMatrix a * U) i i).re := by
  simp only [polarization.eq_1, spinMatrix.eq_1,
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy.eq_1,
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jz.eq_1]
  fin_cases a <;>
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

private lemma spin_trace (a : Fin 3) : (spinMatrix a).trace = 0 := by
  fin_cases a <;>
    norm_num [spinMatrix, Matrix.trace, Fin.sum_univ_succ,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jplus,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jx,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy,
      D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jz]

private lemma conjugated_spin_trace (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (a : Fin 3) :
    (Uᴴ * spinMatrix a * U).trace = 0 := by
  rw [Matrix.trace_mul_cycle, show U * Uᴴ = 1 from hU.2,
    Matrix.one_mul, spin_trace]

private lemma polarization_pair (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (hdet : U.det = 1) (a k : Fin 3) :
    ((fun i => (transported U i (evenIndex k)).re) ⬝ᵥ
      (generator a *ᵥ fun i => (transported U i (oddIndex k)).re)) =
      polarization (fun j => U j 0) a + polarization (fun j => U j k.succ) a := by
  have hB := realBasis_identities.1
  have hBB : realBasis * realBasisᴴ = 1 := mul_eq_one_comm.mp hB
  have hcov : (transported U)ᴴ * (generator a).map Complex.ofReal * transported U =
      realBasisᴴ * ((-I : ℂ) • liftSpin (Uᴴ * spinMatrix a * U)) * realBasis := by
    calc
      _ = realBasisᴴ * ((compound U)ᴴ * ((-I : ℂ) • liftSpin (spinMatrix a)) *
          compound U) * realBasis := by
        rw [← generator_bridge]
        simp only [transported.eq_1, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        simp only [← Matrix.mul_assoc realBasis realBasisᴴ, hBB, Matrix.one_mul]
      _ = _ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, compound_one_body U _ hU]
  have he := congrArg
    (fun M : Matrix (Fin 6) (Fin 6) ℂ => M (evenIndex k) (oddIndex k)) hcov
  rw [lift_pair_entry _ (conjugated_spin_trace U hU a)] at he
  rw [polarization_diagonal, polarization_diagonal]
  rw [← Complex.add_re, ← he]
  have hr := (transported_real_orthogonal U hU hdet).1
  norm_num [dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, hr]
  ring

private lemma transport_identity (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) (hdet : U.det = 1) :
    (∑ i : Fin 4, ∑ a : Fin 3, polarization (fun j => U j i) a ^ 2) =
      2 * ∑ k : Fin 3,
        RHLinalg.frobSq
          (shape (fun i => (transported U i (evenIndex k)).re) *
              shape (fun i => (transported U i (oddIndex k)).re) -
            shape (fun i => (transported U i (oddIndex k)).re) *
              shape (fun i => (transported U i (evenIndex k)).re)) := by
  have hz (a : Fin 3) : ∑ i : Fin 4, polarization (fun j => U j i) a = 0 := by
    simp_rw [polarization_diagonal]
    simpa [Matrix.trace] using congrArg Complex.re (conjugated_spin_trace U hU a)
  have hs (a : Fin 3) : (∑ i : Fin 4, polarization (fun j => U j i) a ^ 2) =
      ∑ k : Fin 3, (polarization (fun j => U j 0) a +
        polarization (fun j => U j k.succ) a) ^ 2 := by
    have h := hz a
    norm_num [Fin.sum_univ_succ] at h ⊢
    linear_combination -2 * polarization (fun j => U j 0) a * h
  rw [Finset.sum_comm]
  simp_rw [hs, ← polarization_pair U hU hdet]
  rw [Finset.sum_comm]
  simp_rw [commutator_coordinates]
  exact (Finset.mul_sum ..).symm

private lemma universal_bound (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) : 1 / 9 ≤ basisAnticoherence U := by
  obtain ⟨V, hV, hdet, hbasis⟩ := phase_reduction U hU
  obtain ⟨hreal, horth⟩ := transported_real_orthogonal V hV hdet
  let O : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (transported V i j).re
  have hO : Oᵀ * O = 1 := by
    ext i j
    change (∑ k, O k i * O k j) = _
    have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => (M i j).re) horth
    simpa [Matrix.mul_apply, Complex.mul_re, hreal, O, Matrix.one_apply, Matrix.transpose_apply,
      apply_ite Complex.re] using h
  have hS := frame_bound O hO
  change 2 * ∑ k : Fin 3, RHLinalg.frobSq _ ≤ 8 at hS
  rw [← transport_identity V hV hdet] at hS
  have hnorm (i : Fin 4) : ∑ j, Complex.normSq (V j i) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M i i).re)
      (Matrix.mem_unitaryGroup_iff'.mp hV)
    simpa [Matrix.mul_apply, Complex.mul_re, Complex.normSq_apply] using h
  have he : basisAnticoherence V =
      1 - (∑ i : Fin 4, ∑ a : Fin 3, polarization (fun j => V j i) a ^ 2) / 9 := by
    unfold basisAnticoherence
    simp_rw [dicke_bridge _ (hnorm _)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    norm_num
    ring
  rw [← hbasis, he]
  linarith

theorem result : claim :=
  ⟨universal_bound, classical_unitary, classical_attainment⟩

end D5.S3.Quantum.Measurement.SpinThreeHalvesClassicalBasis
