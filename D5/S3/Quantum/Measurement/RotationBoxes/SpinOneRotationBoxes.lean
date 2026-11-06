/- GID: D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every normalized degree-two rotation family has a single quantum realization. -/

/-
admission_basis: open-problem-resolution (#22872; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26845
Direct frozen dependencies: K0 = D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap; K1 = D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj; K2 = D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply; S = D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState; P = Matrix.trace_submatrix; T = RHLinalg.trace_mul_nonneg_of_posSemidef.
K0 declaration statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7.
K1 declaration statement_id: sha256:beb687a7629ceb256c23382ba2a92cbaaf9290eb18c04844c530f5be33c31fcc.
K2 declaration statement_id: sha256:065ec62ed35c9f042b51d14ac7534229d83240f7252faec6805576b51b620645.
S declaration statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5.
P declaration statement_id: sha256:4a3e6d97d579d72bb43e84a855506fb9fac56ccaa371ab1ac3d19577aae06146.
T declaration statement_id: sha256:d0be9623184a0aa6b2753f04a89d828122fe7292de10124c81506a795f6decf6.
The finite direct-sum carrier is written as a sigma type without a type alias.
The POVM condition is expanded literally; DensityState is the existing finite-state owner.
proof_shape: reverseAverage: bind-only; consumers: reverseAverage_posSemidef, simultaneous_diagonal_normalization, reverseAverage_preserves, reverseAverage_entries; frozen: none
proof_shape: gramPolynomial: bind-only; consumers: quantum_rotation, normalized_nonnegative_trig2_grams, simultaneous_diagonal_normalization, rotation_quantum, reverseAverage_preserves, born_block_polynomial, gramPolynomial_add, gramPolynomial_smul, gram_family_quantum, zeroFactorGram_polynomial, gramPolynomial_sum, gramPolynomial_real, shiftGram_polynomial, gramPolynomial_evaluation, diagonal_whitening_evaluation, gramPolynomial_coefficients, nonnegative_trig2_gram, gramPolynomial_phase; frozen: none
proof_shape: reverseAverage_posSemidef: bind-only; consumers: simultaneous_diagonal_normalization; frozen: none
proof_shape: reverseAverage_preserves: bind-only; consumers: simultaneous_diagonal_normalization; frozen: none
proof_shape: reverseAverage_entries: bind-only; consumers: simultaneous_diagonal_normalization; frozen: none
proof_shape: degree_two_uniqueness: bind-only; consumers: gramPolynomial_coefficients; frozen: none
proof_shape: gramPolynomial_coefficients: bind-only; consumers: simultaneous_diagonal_normalization; frozen: none
proof_shape: gramPolynomial_sum: bind-only; consumers: simultaneous_diagonal_normalization, gramPolynomial_add; frozen: none
proof_shape: simultaneous_diagonal_normalization: bind-only; consumers: normalized_nonnegative_trig2_grams; frozen: none
proof_shape: gramPolynomial_add: bind-only; consumers: zeroFactorGram_polynomial, nonnegative_trig2_gram; frozen: none
proof_shape: gramPolynomial_smul: bind-only; consumers: zeroFactorGram_polynomial, nonnegative_trig2_gram; frozen: none
proof_shape: zeroFactorGram: bind-only; consumers: zeroFactorGram_polynomial, zeroFactorGram_posSemidef, nonnegative_trig2_gram; frozen: none
proof_shape: zeroFactorGram_posSemidef: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: zeroFactorGram_polynomial: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: phase_add: bind-only; consumers: phase_star_mul, shiftGram_polynomial, gramPolynomial_evaluation; frozen: none
proof_shape: phase_neg: bind-only; consumers: phase_star_mul, gramPolynomial_evaluation; frozen: none
proof_shape: phase_star_mul: bind-only; consumers: rotation_unitary, shiftGram_polynomial; frozen: none
proof_shape: shiftGram: bind-only; consumers: shiftGram_polynomial, shiftGram_posSemidef, nonnegative_trig2_gram; frozen: K0,K1
proof_shape: shiftGram_posSemidef: bind-only; consumers: nonnegative_trig2_gram; frozen: K0,K1,K2
proof_shape: gramPolynomial_phase: bind-only; consumers: shiftGram_polynomial, gramPolynomial_evaluation; frozen: none
proof_shape: shiftGram_polynomial: bind-only; consumers: nonnegative_trig2_gram; frozen: K0,K1,K2
proof_shape: trig2: bind-only; consumers: normalized_nonnegative_trig2_grams, trig2_periodic, rotation_quantum, trig2_minimum, trig2_zero_factor, trig2_minimum_derivative, trig2_shift, trig2_deriv_zero, trig2_continuous, nonnegative_trig2_gram; frozen: none
proof_shape: trig2_continuous: bind-only; consumers: trig2_minimum; frozen: none
proof_shape: trig2_periodic: bind-only; consumers: trig2_minimum; frozen: none
proof_shape: trig2_minimum: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: trig2_deriv_zero: bind-only; consumers: trig2_minimum_derivative; frozen: none
proof_shape: trig2_minimum_derivative: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: trig2_shift: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: trig2_zero_factor: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: linear_trig_nonnegative_of_product: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: linear_trig_norm_bound: bind-only; consumers: nonnegative_trig2_gram; frozen: none
proof_shape: nonnegative_trig2_gram: bind-only; consumers: normalized_nonnegative_trig2_grams; frozen: K0,K1,K2
proof_shape: normalized_nonnegative_trig2_grams: bind-only; consumers: rotation_quantum; frozen: K0,K1,K2
proof_shape: psd_zero_diagonal_row_col: bind-only; consumers: diagonal_sum_support; frozen: none
proof_shape: diagonal_sum_support: bind-only; consumers: supported_whitening; frozen: none
proof_shape: diagonal_root_inverse: bind-only; consumers: supported_whitening; frozen: none
proof_shape: inverse_root_normalization: bind-only; consumers: diagonal_whitening_povm; frozen: none
proof_shape: root_complement_zero: bind-only; consumers: diagonal_whitening_povm; frozen: none
proof_shape: supported_whitening: bind-only; consumers: diagonal_whitening_povm; frozen: none
proof_shape: diagonal_whitening_povm: bind-only; consumers: gram_family_quantum; frozen: none
proof_shape: QuantumSpinOne: bind-only; consumers: quantum_rotation, rotation_quantum, gram_family_quantum, result, claim; frozen: S
proof_shape: RotationSpinOne: bind-only; consumers: quantum_rotation, rotation_quantum, result, claim; frozen: none
proof_shape: claim: bind-only; consumers: result; frozen: S
proof_shape: gramVector: bind-only; consumers: born_block_polynomial, gram_family_quantum, gramPolynomial_evaluation, diagonal_whitening_evaluation; frozen: none
proof_shape: gramPolynomial_evaluation: bind-only; consumers: born_block_polynomial, diagonal_whitening_evaluation; frozen: none
proof_shape: phase_exp: bind-only; consumers: rotation_eq_phase; frozen: none
proof_shape: rotation_eq_phase: bind-only; consumers: born_block_polynomial, gram_family_quantum, rotation_unitary; frozen: none
proof_shape: rotation_unitary: bind-only; consumers: quantum_rotation; frozen: none
proof_shape: diagonal_pure_trace: bind-only; consumers: gram_family_quantum; frozen: none
proof_shape: diagonal_whitening_evaluation: bind-only; consumers: gram_family_quantum; frozen: none
proof_shape: gram_family_quantum: bind-only; consumers: rotation_quantum; frozen: S,P
proof_shape: bornBlock: bind-only; consumers: quantum_rotation, born_block_polynomial; frozen: none
proof_shape: born_block_polynomial: bind-only; consumers: quantum_rotation; frozen: none
proof_shape: gramPolynomial_real: bind-only; consumers: quantum_rotation; frozen: none
proof_shape: quantum_rotation: bind-only; consumers: result; frozen: S,T
proof_shape: rotation_quantum: bind-only; consumers: result; frozen: K0,K1,K2,S,P
proof_shape: result: bind-only; settling result; frozen: K0,K1,K2,S,P,T
-/
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

noncomputable section

namespace D5.S3.Quantum.Measurement.RotationBoxes.SpinOneRotationBoxes

open Matrix
open scoped BigOperators ComplexOrder

private def reverseAverage (Q : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℝ) • (Q + Q.transpose.submatrix Fin.rev Fin.rev)

private def gramPolynomial (Q : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) : ℂ :=
  Q 0 0 + Q 1 1 + Q 2 2 +
    (Q 0 1 + Q 1 2) * ((Real.cos θ : ℂ) + Complex.I * Real.sin θ) +
    (Q 1 0 + Q 2 1) * ((Real.cos θ : ℂ) - Complex.I * Real.sin θ) +
    Q 0 2 * ((Real.cos (2 * θ) : ℂ) + Complex.I * Real.sin (2 * θ)) +
    Q 2 0 * ((Real.cos (2 * θ) : ℂ) - Complex.I * Real.sin (2 * θ))

private theorem reverseAverage_posSemidef (Q : Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : Q.PosSemidef) : (reverseAverage Q).PosSemidef := by
  exact (hQ.add (hQ.transpose.submatrix Fin.rev)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem reverseAverage_preserves (Q : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    gramPolynomial (reverseAverage Q) θ = gramPolynomial Q θ := by
  simp [gramPolynomial, reverseAverage, Matrix.submatrix_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Complex.real_smul, Fin.rev]
  <;> ring

private theorem reverseAverage_entries (Q : Matrix (Fin 3) (Fin 3) ℂ) :
    reverseAverage Q 0 1 = reverseAverage Q 1 2 ∧
    reverseAverage Q 1 0 = reverseAverage Q 2 1 ∧
    reverseAverage Q 0 0 = reverseAverage Q 2 2 := by
  constructor
  · simp [reverseAverage, Matrix.submatrix_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Complex.real_smul, Fin.rev]
    <;> ring
  constructor
  · simp [reverseAverage, Matrix.submatrix_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Complex.real_smul, Fin.rev]
    <;> ring
  · simp [reverseAverage, Matrix.submatrix_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Complex.real_smul, Fin.rev]
    <;> ring

private theorem degree_two_uniqueness (k a b c d : ℂ)
    (h : ∀ θ : ℝ, k + a * Real.cos θ + b * Real.sin θ +
      c * Real.cos (2 * θ) + d * Real.sin (2 * θ) = 1) :
    k = 1 ∧ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h0 := h 0
  have hp := h Real.pi
  have hh := h (Real.pi / 2)
  have hn := h (-(Real.pi / 2))
  norm_num [Real.cos_two_mul, Real.sin_two_mul] at h0 hp hh hn
  have ha : a = 0 := by linear_combination (h0 - hp) / 2
  have hb : b = 0 := by linear_combination (hh - hn) / 2
  have hc : c = 0 := by linear_combination (h0 + hp - hh - hn) / 4
  have hk : k = 1 := by linear_combination (h0 + hp + hh + hn) / 4
  have hq := h (Real.pi / 4)
  rw [ha, hb, hc, hk] at hq
  have hangle : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  norm_num [hangle] at hq
  exact ⟨hk, ha, hb, hc, by linear_combination hq⟩

private theorem gramPolynomial_coefficients (C : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ θ, gramPolynomial C θ = 1) :
    Matrix.trace C = 1 ∧ C 0 1 + C 1 2 = 0 ∧ C 1 0 + C 2 1 = 0 ∧
      C 0 2 = 0 ∧ C 2 0 = 0 := by
  let u := C 0 1 + C 1 2
  let v := C 1 0 + C 2 1
  obtain ⟨hk, ha, hb, hc, hd⟩ := degree_two_uniqueness
    (C 0 0 + C 1 1 + C 2 2) (u + v) (Complex.I * (u - v))
    (C 0 2 + C 2 0) (Complex.I * (C 0 2 - C 2 0)) (by
      intro θ
      convert h θ using 1 <;> dsimp [gramPolynomial, u, v] <;> ring)
  have huv : u - v = 0 := (mul_eq_zero.mp hb).resolve_left Complex.I_ne_zero
  have h02 : C 0 2 - C 2 0 = 0 :=
    (mul_eq_zero.mp hd).resolve_left Complex.I_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Matrix.trace, Fin.sum_univ_three] using hk
  · change u = 0
    linear_combination (ha + huv) / 2
  · change v = 0
    linear_combination (ha - huv) / 2
  · linear_combination (hc + h02) / 2
  · linear_combination (hc - h02) / 2

private theorem gramPolynomial_sum {A : Type} [Fintype A]
    (Q : A → Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    gramPolynomial (∑ a, Q a) θ = ∑ a, gramPolynomial (Q a) θ := by
  simp [gramPolynomial, Matrix.sum_apply, add_mul, Finset.sum_add_distrib, Finset.sum_mul]

private theorem simultaneous_diagonal_normalization {A : Type} [Fintype A]
    (Q : A → Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : ∀ a, (Q a).PosSemidef)
    (hnorm : ∀ θ, (∑ a, gramPolynomial (Q a) θ) = 1) :
    ∃ B : A → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ a, (B a).PosSemidef) ∧
      (∀ a θ, gramPolynomial (B a) θ = gramPolynomial (Q a) θ) ∧
      (∑ a, B a) = Matrix.diagonal (fun i => (∑ a, B a) i i) ∧
      Matrix.trace (∑ a, B a) = 1 ∧ (∑ a, B a) 0 0 = (∑ a, B a) 2 2 := by
  let B := fun a => reverseAverage (Q a)
  let C := ∑ a, B a
  have hc : ∀ θ, gramPolynomial C θ = 1 := by
    intro θ
    dsimp [C]
    rw [gramPolynomial_sum]
    simpa only [B, reverseAverage_preserves] using hnorm θ
  obtain ⟨ht, hu, hv, hw, hz⟩ := gramPolynomial_coefficients C hc
  have he1 : C 0 1 = C 1 2 := by
    dsimp [C]
    simp only [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (reverseAverage_entries (Q a)).1
  have he2 : C 1 0 = C 2 1 := by
    dsimp [C]
    simp only [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (reverseAverage_entries (Q a)).2.1
  have he0 : C 0 0 = C 2 2 := by
    dsimp [C]
    simp only [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (reverseAverage_entries (Q a)).2.2
  have h01 : C 0 1 = 0 := by rw [← he1] at hu; linear_combination hu / 2
  have h12 : C 1 2 = 0 := he1.symm.trans h01
  have h10 : C 1 0 = 0 := by rw [← he2] at hv; linear_combination hv / 2
  have h21 : C 2 1 = 0 := he2.symm.trans h10
  refine ⟨B, (fun a => reverseAverage_posSemidef _ (hQ a)),
    (fun a θ => reverseAverage_preserves _ θ), ?_, ht, he0⟩
  change C = Matrix.diagonal (fun i => C i i)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, h01, h12, h10, h21, hw, hz]

private theorem gramPolynomial_add (Q R : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    gramPolynomial (Q + R) θ = gramPolynomial Q θ + gramPolynomial R θ := by
  simpa [Fintype.sum_bool] using
    (gramPolynomial_sum (fun b : Bool => if b then Q else R) θ)

private theorem gramPolynomial_smul (r : ℝ) (Q : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    gramPolynomial (r • Q) θ = (r : ℂ) * gramPolynomial Q θ := by
  simp [gramPolynomial, Matrix.smul_apply, Complex.real_smul]
  ring

private def zeroFactorGram (a r β : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((a-r)/2 : ℝ) • Matrix.vecMulVec (star ![1, -1, 0]) ![1, -1, 0] +
    (r/4 : ℝ) • Matrix.vecMulVec (star ![1, (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-β) - 1, -(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-β)]) ![1, (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-β) - 1, -(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-β)]

private theorem zeroFactorGram_posSemidef (a r β : ℝ) (hr : 0 ≤ r) (ha : r ≤ a) :
    (zeroFactorGram a r β).PosSemidef := by
  exact ((Matrix.posSemidef_vecMulVec_star_self _).smul (by positivity : 0 ≤ (a-r)/2)).add
    ((Matrix.posSemidef_vecMulVec_star_self _).smul (by positivity : 0 ≤ r/4))

private theorem zeroFactorGram_polynomial (a r β θ : ℝ) :
    gramPolynomial (zeroFactorGram a r β) θ =
      (((1-Real.cos θ) * (a + r * Real.cos β * Real.cos θ +
        r * Real.sin β * Real.sin θ) : ℝ) : ℂ) := by
  rw [zeroFactorGram, gramPolynomial_add, gramPolynomial_smul, gramPolynomial_smul]
  apply Complex.ext
  · simp [gramPolynomial, Matrix.vecMulVec, Real.cos_neg, Real.sin_neg,
      Real.cos_two_mul, Real.sin_two_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
    linear_combination (r * (1-Real.cos θ) / 2) * (Real.cos_sq_add_sin_sq β)
  · simp [gramPolynomial, Matrix.vecMulVec, Real.cos_neg, Real.sin_neg,
      Real.cos_two_mul, Real.sin_two_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
    <;> ring_nf <;> simp

private theorem phase_add (θ α : ℝ) : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (θ+α) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α := by
  apply Complex.ext <;> simp [ Real.cos_add, Real.sin_add,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im] <;> ring

private theorem phase_neg (θ : ℝ) : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) = star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) := by
  simp [ Real.cos_neg, Real.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem phase_star_mul (θ : ℝ) : star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ = 1 := by
  rw [← phase_neg, ← phase_add]
  simp []

private def shiftGram (Q : Matrix (Fin 3) (Fin 3) ℂ) (α : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let D := Matrix.diagonal ![(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α, 1, (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)]
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj Dᴴ Q

private theorem shiftGram_posSemidef (Q : Matrix (Fin 3) (Fin 3) ℂ) (hQ : Q.PosSemidef)
    (α : ℝ) : (shiftGram Q α).PosSemidef := by
  simp only [shiftGram,
    D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply,
    Matrix.conjTranspose_conjTranspose]
  exact hQ.conjTranspose_mul_mul_same _

private theorem gramPolynomial_phase (Q : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    gramPolynomial Q θ = Q 0 0 + Q 1 1 + Q 2 2 +
      (Q 0 1+Q 1 2)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ + (Q 1 0+Q 2 1)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) +
      Q 0 2*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (2*θ) + Q 2 0*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-(2*θ)) := by
  simp only [gramPolynomial, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

private theorem shiftGram_polynomial (Q : Matrix (Fin 3) (Fin 3) ℂ) (α θ : ℝ) :
    gramPolynomial (shiftGram Q α) θ = gramPolynomial Q (θ-α) := by
  have hd (i : Fin 3) : shiftGram Q α i i = Q i i := by
    fin_cases i
    · simp only [shiftGram,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.diagonal_conjTranspose, Pi.star_apply, star_star,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      change star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α) * Q 0 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α = Q 0 0
      calc
        _ = Q 0 0 * (star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α) * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α) := by ring
        _ = _ := by rw [phase_star_mul, mul_one]
    · simp [shiftGram,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal]
    · simp only [shiftGram,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.diagonal_conjTranspose, Pi.star_apply, star_star,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      change star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)) * Q 2 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α) = Q 2 2
      calc
        _ = Q 2 2 * (star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)) * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)) := by ring
        _ = _ := by rw [phase_star_mul, mul_one]
  have h1 : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (θ-α) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ := by
    rw [← phase_add]; congr 1 <;> ring
  have h1n : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (α-θ) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) := by
    rw [← phase_add]; congr 1 <;> ring
  have h2 : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (2*(θ-α)) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-α)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (2*θ) := by
    rw [← phase_add, ← phase_add]; congr 1 <;> ring
  have h2n : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-(2*(θ-α))) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) α*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-(2*θ)) := by
    rw [← phase_add, ← phase_add]; congr 1 <;> ring
  simp only [gramPolynomial_phase, hd]
  simp only [shiftGram,
      D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.conj_apply, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_conjTranspose, Pi.star_apply, ← phase_neg,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_fin_one, star_star, star_one,
    neg_neg, neg_sub]
  simp only [h1, h1n, h2, h2n]
  ring

open Set Filter
open scoped Topology

private def trig2 (c₀ c₁ s₁ c₂ s₂ θ : ℝ) : ℝ :=
  c₀ + c₁ * Real.cos θ + s₁ * Real.sin θ +
    c₂ * Real.cos (2 * θ) + s₂ * Real.sin (2 * θ)

private theorem trig2_continuous (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    Continuous (trig2 c₀ c₁ s₁ c₂ s₂) := by
  unfold trig2
  fun_prop

private theorem trig2_periodic (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    Function.Periodic (trig2 c₀ c₁ s₁ c₂ s₂) (2 * Real.pi) := by
  intro θ
  norm_num [trig2, Real.cos_two_mul, Real.sin_two_mul, Real.cos_add, Real.sin_add]

private theorem trig2_minimum (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    ∃ α : ℝ, ∀ θ, trig2 c₀ c₁ s₁ c₂ s₂ α ≤ trig2 c₀ c₁ s₁ c₂ s₂ θ := by
  let f := trig2 c₀ c₁ s₁ c₂ s₂
  have hc : IsCompact (range f) :=
    (trig2_periodic c₀ c₁ s₁ c₂ s₂).compact_of_continuous
      (ne_of_gt Real.two_pi_pos) (trig2_continuous c₀ c₁ s₁ c₂ s₂)
  obtain ⟨m, ⟨α, hα⟩, hm⟩ := hc.exists_isMinOn (range_nonempty f) continuous_id.continuousOn
  refine ⟨α, fun θ => ?_⟩
  change f α ≤ f θ
  rw [hα]
  exact hm (mem_range_self θ)

private theorem trig2_deriv_zero (c₀ c₁ s₁ c₂ s₂ : ℝ) :
    HasDerivAt (trig2 c₀ c₁ s₁ c₂ s₂) (s₁ + 2 * s₂) 0 := by
  have h := ((((hasDerivAt_const (0 : ℝ) c₀).add
    ((Real.hasDerivAt_cos 0).const_mul c₁)).add
    ((Real.hasDerivAt_sin 0).const_mul s₁)).add
    ((((hasDerivAt_id (0 : ℝ)).const_mul 2).cos).const_mul c₂)).add
    ((((hasDerivAt_id (0 : ℝ)).const_mul 2).sin).const_mul s₂)
  convert h using 1 <;> simp [Pi.add_def, mul_comm]
  funext x
  simp [trig2, mul_comm]

private theorem trig2_minimum_derivative (c₀ c₁ s₁ c₂ s₂ : ℝ)
    (hm : ∀ θ, trig2 c₀ c₁ s₁ c₂ s₂ 0 ≤ trig2 c₀ c₁ s₁ c₂ s₂ θ) :
    s₁ + 2 * s₂ = 0 := by
  have hlocal : IsLocalMin (trig2 c₀ c₁ s₁ c₂ s₂) 0 :=
    Filter.Eventually.of_forall hm
  exact (trig2_deriv_zero c₀ c₁ s₁ c₂ s₂).deriv.symm.trans hlocal.deriv_eq_zero

private theorem trig2_shift (c₀ c₁ s₁ c₂ s₂ α m θ : ℝ) :
    trig2 c₀ c₁ s₁ c₂ s₂ (θ + α) - m =
      trig2 (c₀ - m) (c₁ * Real.cos α + s₁ * Real.sin α)
        (-c₁ * Real.sin α + s₁ * Real.cos α)
        (c₂ * Real.cos (2 * α) + s₂ * Real.sin (2 * α))
        (-c₂ * Real.sin (2 * α) + s₂ * Real.cos (2 * α)) θ := by
  simp only [trig2, mul_add, Real.cos_add, Real.sin_add]
  ring

private theorem trig2_zero_factor (c₀ c₁ s₁ c₂ s₂ : ℝ)
    (h0 : trig2 c₀ c₁ s₁ c₂ s₂ 0 = 0) (hd : s₁ + 2 * s₂ = 0) (θ : ℝ) :
    trig2 c₀ c₁ s₁ c₂ s₂ θ =
      (1 - Real.cos θ) * (c₀ - c₂ - 2 * c₂ * Real.cos θ - 2 * s₂ * Real.sin θ) := by
  norm_num [trig2] at h0
  have hc₀ : c₀ = -c₁ - c₂ := by linarith
  have hs₁ : s₁ = -2 * s₂ := by linarith
  simp only [trig2, Real.cos_two_mul, Real.sin_two_mul, hc₀, hs₁]
  ring

private theorem linear_trig_nonnegative_of_product (a b c : ℝ)
    (h : ∀ θ, 0 ≤ (1 - Real.cos θ) * (a + b * Real.cos θ + c * Real.sin θ)) :
    ∀ θ, 0 ≤ a + b * Real.cos θ + c * Real.sin θ := by
  have haway (θ : ℝ) (hθ : Real.cos θ ≠ 1) :
      0 ≤ a + b * Real.cos θ + c * Real.sin θ := by
    have hp : 0 < 1 - Real.cos θ := sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one θ) hθ)
    exact nonneg_of_mul_nonneg_right (h θ) hp
  have hc : Continuous (fun θ => a + b * Real.cos θ + c * Real.sin θ) := by fun_prop
  have hzero : 0 ≤ a + b := by
    have ht : Tendsto (fun θ : ℝ => a + b * Real.cos θ + c * Real.sin θ)
        (𝓝[>] (0 : ℝ)) (𝓝 (a+b)) := by
      simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hn : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 ≤ a + b * Real.cos θ + c * Real.sin θ := by
      filter_upwards [Ioo_mem_nhdsGT Real.two_pi_pos] with θ hθ
      apply haway θ
      exact (Real.cos_eq_one_iff_of_lt_of_lt (x := θ)
        (by linarith [Real.pi_pos, hθ.1]) hθ.2).not.mpr (ne_of_gt hθ.1)
    exact ge_of_tendsto ht hn
  intro θ
  by_cases hθ : Real.cos θ = 1
  · have hs : Real.sin θ = 0 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    simpa [hθ, hs] using hzero
  · exact haway θ hθ

private theorem linear_trig_norm_bound (a b c : ℝ)
    (h : ∀ θ, 0 ≤ a + b * Real.cos θ + c * Real.sin θ) :
    ‖(b : ℂ) + Complex.I * c‖ ≤ a := by
  let z : ℂ := (b : ℂ) + Complex.I * c
  let r : ℝ := ‖z‖
  let β : ℝ := Complex.arg z
  have hb : r * Real.cos β = b := by
    simpa [r, β, z, Complex.mul_re] using Complex.norm_mul_cos_arg z
  have hc : r * Real.sin β = c := by
    simpa [r, β, z, Complex.mul_im] using Complex.norm_mul_sin_arg z
  have hn : 0 ≤ r := norm_nonneg z
  have htest := h (β + Real.pi)
  rw [Real.cos_add_pi, Real.sin_add_pi] at htest
  change r ≤ a
  calc
    r = r * (Real.cos β ^ 2 + Real.sin β ^ 2) := by rw [Real.cos_sq_add_sin_sq, mul_one]
    _ = b * Real.cos β + c * Real.sin β := by rw [← hb, ← hc]; ring
    _ ≤ a := by linarith

open Matrix
open scoped BigOperators ComplexOrder

private theorem nonnegative_trig2_gram (c₀ c₁ s₁ c₂ s₂ : ℝ)
    (hn : ∀ θ, 0 ≤ trig2 c₀ c₁ s₁ c₂ s₂ θ) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℂ, Q.PosSemidef ∧
      ∀ θ, gramPolynomial Q θ = (trig2 c₀ c₁ s₁ c₂ s₂ θ : ℂ) := by
  let f := trig2 c₀ c₁ s₁ c₂ s₂
  obtain ⟨α, hα⟩ := trig2_minimum c₀ c₁ s₁ c₂ s₂
  let m := f α
  let C₀ := c₀-m
  let C₁ := c₁*Real.cos α+s₁*Real.sin α
  let S₁ := -c₁*Real.sin α+s₁*Real.cos α
  let C₂ := c₂*Real.cos (2*α)+s₂*Real.sin (2*α)
  let S₂ := -c₂*Real.sin (2*α)+s₂*Real.cos (2*α)
  let q := trig2 C₀ C₁ S₁ C₂ S₂
  have hshift (θ : ℝ) : q θ = f (θ+α)-m :=
    (trig2_shift c₀ c₁ s₁ c₂ s₂ α m θ).symm
  have h0 : q 0 = 0 := by rw [hshift]; simp [m]
  have hmin (θ : ℝ) : q 0 ≤ q θ := by
    rw [hshift, hshift]
    simp only [zero_add]
    exact sub_le_sub_right (hα _) m
  have hd : S₁+2*S₂ = 0 := trig2_minimum_derivative C₀ C₁ S₁ C₂ S₂ hmin
  have hq (θ : ℝ) : q θ = (1-Real.cos θ)*
      (C₀-C₂ + (-2*C₂)*Real.cos θ+(-2*S₂)*Real.sin θ) := by
    simpa only [sub_eq_add_neg, neg_mul, mul_assoc] using
      trig2_zero_factor C₀ C₁ S₁ C₂ S₂ h0 hd θ
  let a := C₀-C₂
  let b := -2*C₂
  let c := -2*S₂
  have hL : ∀ θ, 0 ≤ a+b*Real.cos θ+c*Real.sin θ := by
    apply linear_trig_nonnegative_of_product
    intro θ
    change 0 ≤ (1-Real.cos θ)*(C₀-C₂+(-2*C₂)*Real.cos θ+(-2*S₂)*Real.sin θ)
    rw [← hq, hshift]
    exact sub_nonneg.mpr (hα _)
  let z : ℂ := (b : ℂ)+Complex.I*c
  let r := ‖z‖
  let β := Complex.arg z
  have hr : 0 ≤ r := norm_nonneg z
  have ha : r ≤ a := linear_trig_norm_bound a b c hL
  have hb : r*Real.cos β = b := by
    simpa [r, β, z] using Complex.norm_mul_cos_arg z
  have hc : r*Real.sin β = c := by
    simpa [r, β, z] using Complex.norm_mul_sin_arg z
  let Q := m • Matrix.vecMulVec (star ![0,1,0]) ![0,1,0] + zeroFactorGram a r β
  have hQ : Q.PosSemidef :=
    ((Matrix.posSemidef_vecMulVec_star_self _).smul (hn α)).add (zeroFactorGram_posSemidef a r β hr ha)
  have hp (θ : ℝ) : gramPolynomial Q θ = (f (θ+α) : ℂ) := by
    change gramPolynomial (m • Matrix.vecMulVec (star ![0,1,0]) ![0,1,0] +
      zeroFactorGram a r β) θ = _
    rw [gramPolynomial_add, gramPolynomial_smul, zeroFactorGram_polynomial, hb, hc]
    have he : gramPolynomial (Matrix.vecMulVec (star ![0,1,0]) ![0,1,0]) θ = 1 := by
      simp [gramPolynomial, Matrix.vecMulVec]
    rw [he, mul_one]
    change (m : ℂ)+(((1-Real.cos θ)*(a+b*Real.cos θ+c*Real.sin θ) : ℝ) : ℂ) = _
    change (m : ℂ)+(((1-Real.cos θ)*(C₀-C₂+(-2*C₂)*Real.cos θ+(-2*S₂)*Real.sin θ) : ℝ) : ℂ) = _
    rw [← hq, hshift]
    push_cast
    ring
  refine ⟨shiftGram Q α, shiftGram_posSemidef Q hQ α, fun θ => ?_⟩
  rw [shiftGram_polynomial, hp]
  congr 2
  ring

private theorem normalized_nonnegative_trig2_grams {A : Type} [Fintype A]
    (c₀ c₁ s₁ c₂ s₂ : A → ℝ)
    (hn : ∀ a θ, 0 ≤ trig2 (c₀ a) (c₁ a) (s₁ a) (c₂ a) (s₂ a) θ)
    (hs : ∀ θ, ∑ a, trig2 (c₀ a) (c₁ a) (s₁ a) (c₂ a) (s₂ a) θ = 1) :
    ∃ B : A → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ a, (B a).PosSemidef) ∧
      (∀ a θ, gramPolynomial (B a) θ = (trig2 (c₀ a) (c₁ a) (s₁ a) (c₂ a) (s₂ a) θ : ℂ)) ∧
      (∑ a, B a) = Matrix.diagonal (fun i => (∑ a, B a) i i) ∧
      Matrix.trace (∑ a, B a) = 1 := by
  classical
  choose Q hQ hp using fun a => nonnegative_trig2_gram (c₀ a) (c₁ a) (s₁ a) (c₂ a) (s₂ a) (hn a)
  have hnorm (θ : ℝ) : ∑ a, gramPolynomial (Q a) θ = 1 := by
    simp only [hp, ← Complex.ofReal_sum]
    exact_mod_cast hs θ
  obtain ⟨B, hB, hpoly, hdiag, htrace, _⟩ := simultaneous_diagonal_normalization Q hQ hnorm
  exact ⟨B, hB, fun a θ => (hpoly a θ).trans (hp a θ), hdiag, htrace⟩

open Matrix
open scoped BigOperators ComplexOrder

variable {A N : Type} [Fintype A] [Fintype N] [DecidableEq N]

private theorem psd_zero_diagonal_row_col (B : Matrix N N ℂ) (hB : B.PosSemidef)
    (i : N) (hi : B i i = 0) : (∀ j, B i j = 0) ∧ ∀ j, B j i = 0 := by
  have hv : B *ᵥ Pi.single i (1 : ℂ) = 0 := by
    apply hB.dotProduct_mulVec_zero_iff.mp
    simpa [Matrix.mulVec_single_one] using hi
  have hcol (j : N) : B j i = 0 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using congrFun hv j
  refine ⟨fun j => ?_, hcol⟩
  have hherm := congrArg (fun M : Matrix N N ℂ => M i j) hB.isHermitian.eq
  simpa [Matrix.conjTranspose_apply, hcol j] using hherm.symm

private theorem diagonal_sum_support (B : A → Matrix N N ℂ) (hB : ∀ a, (B a).PosSemidef)
    (c : N → ℝ) (hsum : ∑ a, B a = Matrix.diagonal (fun i => (c i : ℂ))) :
    ∀ a, (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) * B a * (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) = B a := by
  have hz (i : N) (hi : c i = 0) (a : A) : B a i i = 0 := by
    have hs : ∑ a, (B a i i).re = 0 := by
      have he := congrArg (fun M : Matrix N N ℂ => (M i i).re) hsum
      simpa [Matrix.sum_apply, hi, Complex.re_sum] using he
    have hr := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ Finset.univ) => (Complex.nonneg_iff.mp (hB a).diag_nonneg).1)).mp hs a (Finset.mem_univ a)
    exact Complex.ext hr (Complex.nonneg_iff.mp (hB a).diag_nonneg).2.symm
  intro a
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : c i = 0
  · simp [hi, (psd_zero_diagonal_row_col _ (hB a) i (hz i hi a)).1 j]
  by_cases hj : c j = 0
  · simp [hj, (psd_zero_diagonal_row_col _ (hB a) j (hz j hj a)).2 i]
  simp [hi, hj]

private theorem diagonal_root_inverse (c : N → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) = (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) ∧
    (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) = (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) := by
  have he (i : N) : (Real.sqrt (c i) : ℂ) * (Real.sqrt (c i) : ℂ)⁻¹ =
      if c i = 0 then 0 else 1 := by
    by_cases hi : c i = 0
    · simp [hi]
    · have hn : (Real.sqrt (c i) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hc i) (Ne.symm hi)))
      simp [hi, hn]
  constructor
  · ext i j
    by_cases h : i = j
    · subst j; simpa [] using he i
    · simp [Matrix.diagonal_mul, h]
  · ext i j
    by_cases h : i = j
    · subst j
      simpa [mul_comm] using he i
    · simp [Matrix.diagonal_mul, h]

private theorem inverse_root_normalization (c : N → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) * Matrix.diagonal (fun i => (c i : ℂ)) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) =
      (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : c i = 0
    · simp [hi]
    have hs : (Real.sqrt (c i) : ℂ) ^ 2 = (c i : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hc i)
    have hn : (Real.sqrt (c i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hc i) (Ne.symm hi)))
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply_eq, if_neg hi]
    rw [← hs]
    field_simp
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hij]

private theorem root_complement_zero (c : N → ℝ) :
    (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) * (1 - (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1))) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) = 0 := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.zero_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : c i = 0 <;> simp [hi]
  · simp [hij]

private theorem supported_whitening (B : A → Matrix N N ℂ) (hB : ∀ a, (B a).PosSemidef)
    (c : N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ a, B a = Matrix.diagonal (fun i => (c i : ℂ))) (a : A) :
    (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) * ((Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) * B a * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹))) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) = B a := by
  calc
    _ = ((Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹))) * B a *
        ((Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)))) := by noncomm_ring
    _ = (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) * B a * (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1)) := by
      rw [(diagonal_root_inverse c hc).1, (diagonal_root_inverse c hc).2]
    _ = B a := diagonal_sum_support B hB c hsum a

private theorem diagonal_whitening_povm [Nonempty A]
    (B : A → Matrix N N ℂ) (hB : ∀ a, (B a).PosSemidef)
    (c : N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ a, B a = Matrix.diagonal (fun i => (c i : ℂ))) :
    ∃ E : A → Matrix N N ℂ,
      (∀ a, (E a).PosSemidef) ∧ ∑ a, E a = 1 ∧
        ∀ a, (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) * E a * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) = B a := by
  let P := (Matrix.diagonal (fun i => if c i = 0 then (0 : ℂ) else 1))
  let M := (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹))
  let w : ℝ := (Fintype.card A : ℝ)⁻¹
  let E := fun a => M * B a * M + w • (1 - P)
  have hcomp : (1 - P).PosSemidef := by
    have he : 1 - P = Matrix.diagonal (fun i => if c i = 0 then (1 : ℂ) else 0) := by
      ext i j
      by_cases hij : i = j
      · subst j; dsimp [P]; simp; split_ifs <;> norm_num
      · simp [P, Matrix.diagonal, hij]
    rw [he, Matrix.posSemidef_diagonal_iff]
    intro i
    split_ifs <;> norm_num
  have hM : M.IsHermitian := by
    change (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)).IsHermitian
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    change star ((Real.sqrt (c i) : ℂ)⁻¹) = (Real.sqrt (c i) : ℂ)⁻¹
    simp
  have hweight : ∑ _a : A, w • (1 - P) = 1 - P := by
    have hn : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, w, Complex.ofReal_inv, Complex.ofReal_natCast]
    field_simp
  refine ⟨E, ?_, ?_, ?_⟩
  · intro a
    have hp := (hB a).conjTranspose_mul_mul_same M
    rw [hM.eq] at hp
    exact hp.add (hcomp.smul (inv_nonneg.mpr (Nat.cast_nonneg _)))
  · dsimp [E]
    rw [Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
    change (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) * Matrix.diagonal (fun i => (c i : ℂ)) * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)⁻¹)) +
      (∑ _a : A, w • (1 - P)) = 1
    rw [inverse_root_normalization c hc, hweight]
    dsimp [P]
    abel
  · intro a
    dsimp [E, M, P]
    rw [Matrix.mul_add, Matrix.add_mul, supported_whitening B hB c hc hsum a,
      Matrix.mul_smul, Matrix.smul_mul, root_complement_zero, smul_zero, add_zero]

open Matrix
open scoped BigOperators

open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

/-- Definition 1: a single density matrix and a single POVM generate the whole family,
with arbitrary finite multiplicities and the complex trace equal to the real probability. -/
def QuantumSpinOne {A : Type} [Fintype A] (p : A → ℝ → ℝ) : Prop :=
  ∃ multiplicity : Fin 3 → ℕ,
    ∃ ρ : DensityState ((Σ j : Fin 3, Fin (multiplicity j))),
      ∃ E : A → Matrix ((Σ j : Fin 3, Fin (multiplicity j))) ((Σ j : Fin 3, Fin (multiplicity j))) ℂ,
        ((∀ a, (E a).PosSemidef) ∧ ∑ a, E a = 1) ∧
          ∀ (a : A) (θ : ℝ),
            Matrix.trace
              ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (multiplicity j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) * CStarMatrix.ofMatrix.symm ρ.1 *
                ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (multiplicity j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))))ᴴ * E a) = (p a θ : ℂ)

/-- Definition 2 at J = 1, with the real Fourier expansion from Lemma 5 and the expansion in §4.2.
Both probability bounds and normalization are imposed for every real angle. -/
def RotationSpinOne {A : Type} [Fintype A] (p : A → ℝ → ℝ) : Prop :=
  (∃ c₀ c₁ s₁ c₂ s₂ : A → ℝ,
    ∀ (a : A) (θ : ℝ),
      p a θ = c₀ a + c₁ a * Real.cos θ + s₁ a * Real.sin θ +
        c₂ a * Real.cos (2 * θ) + s₂ a * Real.sin (2 * θ)) ∧
    (∀ (a : A) (θ : ℝ), 0 ≤ p a θ ∧ p a θ ≤ 1) ∧
    (∀ θ : ℝ, ∑ a : A, p a θ = 1)

/-- The unnumbered open question at the end of §4.2.3, arXiv:2312.09278v2:
Q₁ᴬ = R₁ᴬ for every finite outcome set of cardinality at least three. -/
def claim : Prop :=
  ∀ (A : Type) [Fintype A], 3 ≤ Fintype.card A →
    ∀ p : A → ℝ → ℝ, QuantumSpinOne p ↔ RotationSpinOne p

open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open scoped BigOperators ComplexOrder MatrixOrder

-- Generic finite Gram evaluation.
private def gramVector (θ : ℝ) : Fin 3 → ℂ := ![(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ), 1, (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ]

private theorem gramPolynomial_evaluation (Q : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    gramPolynomial Q θ = star (gramVector θ) ⬝ᵥ (Q *ᵥ gramVector θ) := by
  have hp : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) = 1 := by
    rw [← phase_add]; simp []
  have hpp : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (2*θ) := by rw [← phase_add]; congr 1; ring
  have hnn : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-(2*θ)) := by
    rw [← phase_add]; congr 1; ring
  rw [gramPolynomial_phase]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  change _ = star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ)) * (Q 0 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) + Q 0 1 * 1 + Q 0 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) +
      star (1 : ℂ) * (Q 1 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) + Q 1 1 * 1 + Q 1 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) +
      star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) * (Q 2 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) + Q 2 1 * 1 + Q 2 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ)
  rw [← phase_neg, ← phase_neg]
  simp only [neg_neg, star_one]
  have he : ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ * (Q 0 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) + Q 0 1 * 1 + Q 0 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) +
      1 * (Q 1 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) + Q 1 1 * 1 + Q 1 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ) +
      (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) * (Q 2 0 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ) + Q 2 1 * 1 + Q 2 2 * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ)) =
    Q 0 0 * ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ)) + Q 1 1 + Q 2 2 * ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ * (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ)) +
      (Q 0 1+Q 1 2)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ+(Q 1 0+Q 2 1)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ)+
      Q 0 2*((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ)+Q 2 0*((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ)*(fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (-θ)) := by ring
  rw [he, hp, hpp, hnn]
  ring

private theorem phase_exp (θ : ℝ) : Complex.exp (Complex.I*(θ : ℂ)) = (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) θ := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [ mul_comm, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem rotation_eq_phase (m : Fin 3 → ℕ) (θ : ℝ) :
    (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) = Matrix.diagonal (fun i => (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1 : ℝ)-1)*θ)) := by
  ext i j
  simp only [Matrix.diagonal_apply]
  split_ifs
  · exact phase_exp _
  · rfl

private theorem rotation_unitary (m : Fin 3 → ℕ) (θ : ℝ) :
    ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))))ᴴ * (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) = 1 := by
  rw [rotation_eq_phase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Pi.mul_apply]
      using phase_star_mul (((i.1 : ℝ) - 1) * θ)
  · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

-- Forward realization uses one copy of each of the three weights.
-- The following general trace identity provides the density/POVM bridge.
private theorem diagonal_pure_trace {N : Type} [Fintype N] [DecidableEq N]
    (u v : N → ℂ) (E : Matrix N N ℂ) :
    Matrix.trace (Matrix.diagonal u * Matrix.vecMulVec v (star v) *
      (Matrix.diagonal u)ᴴ * E) =
      star (fun i => u i*v i) ⬝ᵥ (E *ᵥ (fun i => u i*v i)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.trace_vecMulVec, ← Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have hv : Matrix.diagonal u *ᵥ v = fun i => u i*v i :=
    funext (Matrix.mulVec_diagonal u v)
  rw [hv]

private theorem diagonal_whitening_evaluation (c : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    star (fun i => gramVector θ i * (Real.sqrt (c i) : ℂ)) ⬝ᵥ
      (E *ᵥ (fun i => gramVector θ i * (Real.sqrt (c i) : ℂ))) =
      gramPolynomial ((Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ))) * E * (Matrix.diagonal (fun i => (Real.sqrt (c i) : ℂ)))) θ := by
  rw [gramPolynomial_evaluation]
  simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem gram_family_quantum {A : Type} [Fintype A] [Nonempty A]
    (p : A → ℝ → ℝ) (B : A → Matrix (Fin 3) (Fin 3) ℂ)
    (hB : ∀ a, (B a).PosSemidef) (c : Fin 3 → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hs : ∑ a, B a = Matrix.diagonal (fun i => (c i : ℂ)))
    (ht : ∑ i, c i = 1) (hp : ∀ a θ, gramPolynomial (B a) θ = (p a θ : ℂ)) :
    QuantumSpinOne p := by
  classical
  obtain ⟨E,hE,hEs,hEb⟩ := diagonal_whitening_povm B hB c hc hs
  let e := Equiv.sigmaUnique (Fin 3) (fun _ => Fin 1)
  let v : Fin 3 → ℂ := fun i => (Real.sqrt (c i) : ℂ)
  let R := Matrix.vecMulVec v (star v)
  have hR : R.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have htr : Matrix.trace R = 1 := by
    simp only [R, Matrix.trace_vecMulVec, dotProduct, v, Pi.star_apply,
      Complex.star_def, Complex.conj_ofReal]
    have he (i : Fin 3) : (Real.sqrt (c i) : ℂ) * (Real.sqrt (c i) : ℂ) = (c i : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (hc i)
    simp only [he, ← Complex.ofReal_sum, ht, Complex.ofReal_one]
  let ρ : DensityState ((Σ _j : Fin 3, Fin 1)) :=
    ⟨CStarMatrix.ofMatrix (R.submatrix e e),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hR.submatrix e).nonneg,
      (Matrix.trace_submatrix R e).trans htr⟩
  refine ⟨fun _ => 1, ρ, fun a => (E a).submatrix e e, ⟨fun a => (hE a).submatrix e, ?_⟩, ?_⟩
  · calc
      ∑ a, (E a).submatrix e e = (∑ a, E a).submatrix e e := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.submatrix_apply]
      _ = 1 := by rw [hEs]; exact Matrix.submatrix_one_equiv e
  · intro a θ
    have hrot : (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin ((fun _ => 1) j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) = (Matrix.diagonal (gramVector θ)).submatrix e e := by
      rw [rotation_eq_phase]
      ext i j
      obtain ⟨i,ii⟩ := i
      obtain ⟨j,jj⟩ := j
      fin_cases ii; fin_cases jj
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.diagonal_apply, Matrix.submatrix_apply, e, gramVector]
    change Matrix.trace ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin ((fun _ => 1) j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) * R.submatrix e e *
      ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin ((fun _ => 1) j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))))ᴴ * (E a).submatrix e e) = _
    rw [hrot, Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.trace_submatrix]
    rw [diagonal_pure_trace]
    change star (fun i => gramVector θ i * (Real.sqrt (c i) : ℂ)) ⬝ᵥ
      (E a *ᵥ (fun i => gramVector θ i * (Real.sqrt (c i) : ℂ))) = _
    rw [diagonal_whitening_evaluation, hEb, hp]

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

private def bornBlock (m : Fin 3 → ℕ) (R E : Matrix ((Σ j : Fin 3, Fin (m j))) ((Σ j : Fin 3, Fin (m j))) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  ∑ x : Fin (m i), ∑ y : Fin (m j), R ⟨j,y⟩ ⟨i,x⟩ * E ⟨i,x⟩ ⟨j,y⟩

private theorem born_block_polynomial (m : Fin 3 → ℕ)
    (R E : Matrix ((Σ j : Fin 3, Fin (m j))) ((Σ j : Fin 3, Fin (m j))) ℂ) (θ : ℝ) :
    Matrix.trace ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) * R * ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))))ᴴ * E) =
      gramPolynomial (bornBlock m R E) θ := by
  rw [rotation_eq_phase]
  have hentry (i j : (Σ j : Fin 3, Fin (m j))) :
      (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) => (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1:ℝ)-1)*θ)) * R *
        (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) => (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1:ℝ)-1)*θ)))ᴴ) i j =
      (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1:ℝ)-1)*θ) * R i j * star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((j.1:ℝ)-1)*θ)) := by
    simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Pi.star_apply]
  simp only [Matrix.trace, Matrix.diag_apply]
  have ht :
      (∑ i : (Σ j : Fin 3, Fin (m j)), (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) => (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1:ℝ)-1)*θ)) * R *
        (Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) => (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1:ℝ)-1)*θ)))ᴴ * E) i i) =
      ∑ i : (Σ j : Fin 3, Fin (m j)), ∑ j : (Σ j : Fin 3, Fin (m j)),
        (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i.1:ℝ)-1)*θ) * R i j * star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((j.1:ℝ)-1)*θ)) * E j i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.mul_apply]
    simp only [hentry]
  rw [ht]
  simp only [Fintype.sum_sigma]
  -- Group the two finite multiplicity sums before expanding the nine frequencies.
  have he : (∑ i : Fin 3, ∑ x : Fin (m i), ∑ j : Fin 3, ∑ y : Fin (m j),
      (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i:ℝ)-1)*θ) * R ⟨i,x⟩ ⟨j,y⟩ * star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((j:ℝ)-1)*θ)) * E ⟨j,y⟩ ⟨i,x⟩) =
    ∑ i : Fin 3, ∑ j : Fin 3, (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i:ℝ)-1)*θ) * star ((fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((j:ℝ)-1)*θ)) *
      bornBlock m R E j i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [bornBlock, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he, gramPolynomial_evaluation]
  have hv (i : Fin 3) : (fun t : ℝ => (Real.cos t : ℂ) + Complex.I * Real.sin t) (((i:ℝ)-1)*θ) = gramVector θ i := by
    fin_cases i <;> norm_num [gramVector]
  simp only [hv, dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem gramPolynomial_real (Q : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) :
    (gramPolynomial Q θ).re =
      (Q 0 0 + Q 1 1 + Q 2 2).re +
      ((Q 0 1+Q 1 2)+(Q 1 0+Q 2 1)).re*Real.cos θ +
      (Complex.I*((Q 0 1+Q 1 2)-(Q 1 0+Q 2 1))).re*Real.sin θ +
      (Q 0 2+Q 2 0).re*Real.cos (2*θ) +
      (Complex.I*(Q 0 2-Q 2 0)).re*Real.sin (2*θ) := by
  simp [gramPolynomial, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

private theorem quantum_rotation {A : Type} [Fintype A] (p : A → ℝ → ℝ)
    (h : QuantumSpinOne p) : RotationSpinOne p := by
  classical
  obtain ⟨m,ρ,E,hE,hp⟩ := h
  let R := CStarMatrix.ofMatrix.symm ρ.1
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  let Q := fun a => bornBlock m R (E a)
  have hpoly (a : A) (θ : ℝ) : gramPolynomial (Q a) θ = (p a θ : ℂ) :=
    (born_block_polynomial m R (E a) θ).symm.trans (hp a θ)
  have hnonneg (a : A) (θ : ℝ) : 0 ≤ p a θ := by
    have hn := RHLinalg.trace_mul_nonneg_of_posSemidef
      (hR.mul_mul_conjTranspose_same ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))))) (hE.1 a)
    change 0 ≤ (Matrix.trace ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))) * R * ((Matrix.diagonal (fun i : (Σ j : Fin 3, Fin (m j)) =>
      Complex.exp (Complex.I * (((i.1 : ℝ) - 1) * θ : ℝ)))))ᴴ * E a)).re at hn
    rw [hp a θ] at hn
    exact hn
  have hsum (θ : ℝ) : ∑ a, p a θ = 1 := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, Complex.ofReal_one]
    simp only [← hp]
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, hE.2, Matrix.mul_one,
      Matrix.trace_mul_cycle, rotation_unitary, Matrix.one_mul]
    exact ρ.2.2
  refine ⟨?_, ?_, hsum⟩
  · refine ⟨(fun a => (Q a 0 0+Q a 1 1+Q a 2 2).re),
      (fun a => ((Q a 0 1+Q a 1 2)+(Q a 1 0+Q a 2 1)).re),
      (fun a => (Complex.I*((Q a 0 1+Q a 1 2)-(Q a 1 0+Q a 2 1))).re),
      (fun a => (Q a 0 2+Q a 2 0).re),
      (fun a => (Complex.I*(Q a 0 2-Q a 2 0)).re), fun a θ => ?_⟩
    have hr := congrArg Complex.re (hpoly a θ)
    rw [gramPolynomial_real] at hr
    exact hr.symm
  · intro a θ
    refine ⟨hnonneg a θ, ?_⟩
    rw [← hsum θ]
    exact Finset.single_le_sum (fun b _ => hnonneg b θ) (Finset.mem_univ a)

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

private theorem rotation_quantum {A : Type} [Fintype A] [Nonempty A]
    (p : A → ℝ → ℝ) (h : RotationSpinOne p) : QuantumSpinOne p := by
  classical
  obtain ⟨⟨c₀,c₁,s₁,c₂,s₂,hcoeff⟩, hbounds, hnorm⟩ := h
  have hn (a : A) (θ : ℝ) : 0 ≤ trig2 (c₀ a) (c₁ a) (s₁ a) (c₂ a) (s₂ a) θ := by
    change 0 ≤ c₀ a+c₁ a*Real.cos θ+s₁ a*Real.sin θ+
      c₂ a*Real.cos (2*θ)+s₂ a*Real.sin (2*θ)
    rw [← hcoeff a θ]
    exact (hbounds a θ).1
  have hs (θ : ℝ) : ∑ a, trig2 (c₀ a) (c₁ a) (s₁ a) (c₂ a) (s₂ a) θ = 1 := by
    simp only [trig2, ← hcoeff]
    exact hnorm θ
  obtain ⟨B,hB,hpoly,hdiag,htrace⟩ := normalized_nonnegative_trig2_grams c₀ c₁ s₁ c₂ s₂ hn hs
  let C := ∑ a, B a
  let c : Fin 3 → ℝ := fun i => (C i i).re
  have hC : C.PosSemidef := Matrix.posSemidef_sum Finset.univ (fun a _ => hB a)
  have hc (i : Fin 3) : 0 ≤ c i := (Complex.nonneg_iff.mp hC.diag_nonneg).1
  have hi (i : Fin 3) : (C i i).im = 0 := (Complex.nonneg_iff.mp hC.diag_nonneg).2.symm
  have hsum : ∑ a, B a = Matrix.diagonal (fun i => (c i : ℂ)) := by
    rw [hdiag]
    congr 1
    funext i
    apply Complex.ext
    · rfl
    · exact hi i
  have ht : ∑ i, c i = 1 := by
    have he := congrArg Complex.re htrace
    simpa [Matrix.trace, c, C] using he
  apply gram_family_quantum p B hB c hc hsum ht
  intro a θ
  rw [hpoly]
  simpa only [trig2] using congrArg (fun x : ℝ => (x : ℂ)) (hcoeff a θ).symm

theorem result : D5.S3.Quantum.Measurement.RotationBoxes.SpinOneRotationBoxes.claim := by
  intro A _ hA p
  have hpos : 0 < Fintype.card A := lt_of_lt_of_le (by decide : 0 < 3) hA
  letI : Nonempty A := Fintype.card_pos_iff.mp hpos
  exact ⟨quantum_rotation p, rotation_quantum p⟩

end D5.S3.Quantum.Measurement.RotationBoxes.SpinOneRotationBoxes
