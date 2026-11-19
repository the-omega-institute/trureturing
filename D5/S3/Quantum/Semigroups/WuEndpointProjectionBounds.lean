/- GID: D5/S3/Quantum/Semigroups/WuEndpointProjectionBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointProjectionBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace pairing with the signed map is bounded on rank-one and mixed rank projections. -/

import D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.IntervalCases

/-! Trace bounds for the signed endpoint on projections. -/

noncomputable section

open Matrix BigOperators
open scoped InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace WuRankOneEndpointFloor

abbrev EndpointVector := EuclideanSpace ℂ Mode

/-- The matrix of the outer product of a vector with its adjoint. -/
def endpointProjector (v : EndpointVector) : TwoMode :=
  Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))

theorem trace_endpointProjector (v : EndpointVector) :
    (endpointProjector v).trace = (↑(‖v‖ ^ 2) : ℂ) := by
  rw [endpointProjector, Matrix.trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

theorem trace_endpointProjector_mul (u : EndpointVector) (X : TwoMode) :
    (endpointProjector u * X).trace = ⟪u, X.toEuclideanLin u⟫_ℂ := by
  rw [Matrix.trace_mul_comm, endpointProjector, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rfl

theorem conj_endpointProjector (U : TwoMode) (v : EndpointVector) :
    MatrixMap.conj U (endpointProjector v) = endpointProjector (U.toEuclideanLin v) := by
  change U * Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) * Uᴴ = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
  rfl

private theorem trace_projector_product (u v : EndpointVector) :
    (endpointProjector u * endpointProjector v).trace = (↑(‖⟪u, v⟫_ℂ‖ ^ 2) : ℂ) := by
  rw [endpointProjector, endpointProjector, Matrix.vecMulVec_mul_vecMulVec]
  rw [Matrix.trace_vecMulVec, dotProduct_smul, dotProduct_comm (star (WithLp.ofLp u)),
    ← EuclideanSpace.inner_eq_star_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  have hconj := inner_conj_symm (𝕜 := ℂ) v u
  rw [hconj]
  ring

private theorem trace_projector_conj (u v : EndpointVector) (U : TwoMode) :
    (endpointProjector u * MatrixMap.conj U (endpointProjector v)).trace.re =
      ‖⟪u, U.toEuclideanLin v⟫_ℂ‖ ^ 2 := by
  rw [conj_endpointProjector, trace_projector_product, Complex.ofReal_re]

private theorem trace_pauli_re (P Q : TwoMode) (a b : ℝ) :
    (P * endpointConjugationSum (a : ℂ) (b : ℂ) Q).trace.re =
      a ^ 4 * (P * Q).trace.re +
      a ^ 3 * b * (∑ j : Fin 4, (P * MatrixMap.conj (endpointU j) Q).trace.re) +
      a ^ 2 * b ^ 2 * (∑ j : Fin 6, (P * MatrixMap.conj (endpointPair j) Q).trace.re) +
      a * b ^ 3 * (∑ j : Fin 4, (P * MatrixMap.conj (endpointTriple j) Q).trace.re) +
      b ^ 4 * (P * MatrixMap.conj endpointVolume Q).trace.re := by
  simp only [endpointConjugationSum, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.sum_apply, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_sum, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_sum]

private theorem trace_twirl_re (P Q : TwoMode) :
    (P * endpointConjugationSum 1 1 Q).trace.re =
      (P * Q).trace.re +
      (∑ j : Fin 4, (P * MatrixMap.conj (endpointU j) Q).trace.re) +
      (∑ j : Fin 6, (P * MatrixMap.conj (endpointPair j) Q).trace.re) +
      (∑ j : Fin 4, (P * MatrixMap.conj (endpointTriple j) Q).trace.re) +
      (P * MatrixMap.conj endpointVolume Q).trace.re := by
  simpa using trace_pauli_re P Q 1 1

theorem endpointU_unitary_left (j : Fin 4) : (endpointU j)ᴴ * endpointU j = 1 := by
  rw [(endpointU_hermitian j).eq, endpointU_sq]

private theorem unitary_left_mul (A B : TwoMode) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc Aᴴ A, hA, one_mul, hB]

theorem endpointVolume_unitary_left : endpointVolumeᴴ * endpointVolume = 1 := by
  unfold endpointVolume
  exact unitary_left_mul _ _
    (unitary_left_mul _ _ (unitary_left_mul _ _ (endpointU_unitary_left 0)
      (endpointU_unitary_left 1)) (endpointU_unitary_left 2)) (endpointU_unitary_left 3)

private theorem overlap_le_one (u v : EndpointVector) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) u v
  rw [hu, hv, one_mul] at h
  nlinarith [norm_nonneg ⟪u, v⟫_ℂ]

private theorem volume_overlap_le_one (u v : EndpointVector)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖⟪u, endpointVolume.toEuclideanLin v⟫_ℂ‖ ^ 2 ≤ 1 := by
  apply overlap_le_one _ _ hu
  have hI : ⟪endpointVolume.toEuclideanLin v, endpointVolume.toEuclideanLin v⟫_ℂ =
      ⟪v, v⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪v, ((Matrix.toLpLin 2 2 endpointVolumeᴴ) ∘ₗ
      Matrix.toLpLin 2 2 endpointVolume) v⟫_ℂ = _
    rw [← Matrix.toLpLin_mul_same, endpointVolume_unitary_left, Matrix.toLpLin_one,
      LinearMap.id_apply]
  have h : ‖endpointVolume.toEuclideanLin v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)] using
      congrArg (RCLike.re (K := ℂ)) hI
  rw [hv] at h
  nlinarith [norm_nonneg (endpointVolume.toEuclideanLin v)]

private theorem rankOne_arithmetic {a b f₀ f₁ f₂ f₃ f₄ : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b = 1)
    (h₀n : 0 ≤ f₀) (h₁n : 0 ≤ f₁) (h₃n : 0 ≤ f₃) (h₄n : 0 ≤ f₄)
    (h₀ : f₀ ≤ 1) (h₄ : f₄ ≤ 1) (hhead : f₀ + f₁ ≤ 2) (htail : f₄ + f₃ ≤ 2)
    (ht : f₀ + f₁ + f₂ + f₃ + f₄ = 4) :
    let w := a ^ 4 * f₀ + a ^ 3 * b * f₁ + a ^ 2 * b ^ 2 * f₂ + a * b ^ 3 * f₃ + b ^ 4 * f₄
    b ^ 2 ≤ w ∧ w ≤ a ^ 2 := by
  let c₀ := a ^ 3 * (a - b)
  let c₁ := a ^ 2 * b * (a - b)
  let c₂ := a * b ^ 2 * (a - b)
  let c₃ := b ^ 3 * (a - b)
  have ha := hb.trans hba
  have hd := sub_nonneg.mpr hba
  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hhead' : 0 ≤ 3 - (f₀ + f₁) := by linarith only [hhead]
  have htail' : 0 ≤ 3 - (f₄ + f₃) := by linarith only [htail]
  have h₀' := sub_nonneg.mpr h₀
  have h₄' := sub_nonneg.mpr h₄
  dsimp only
  constructor
  · apply sub_nonneg.mp
    have h : b ^ 2 * (a + b) ^ 2 = b ^ 2 := by rw [hab, one_pow, mul_one]
    conv_rhs => arg 2; rw [← h]
    calc
      _ = c₃ * (1 - f₄) + c₂ * (3 - (f₄ + f₃)) + c₁ * (f₀ + f₁) + c₀ * f₀ := by
        dsimp [c₀, c₁, c₂, c₃]
        linear_combination a ^ 2 * b ^ 2 * ht
      _ ≥ 0 := by positivity
  · apply sub_nonneg.mp
    have h : a ^ 2 * (a + b) ^ 2 = a ^ 2 := by rw [hab, one_pow, mul_one]
    conv_rhs => arg 1; rw [← h]
    calc
      _ = c₀ * (1 - f₀) + c₁ * (3 - (f₀ + f₁)) + c₂ * (f₃ + f₄) + c₃ * f₄ := by
        dsimp [c₀, c₁, c₂, c₃]
        linear_combination -a ^ 2 * b ^ 2 * ht
      _ ≥ 0 := by positivity

/-- Exact trace bounds for the signed channel on two arbitrary complex rank-one projections. -/
theorem A₁_rankOne_rankOne (u v : EndpointVector) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    endpointBeta ^ 2 ≤ (endpointProjector u * A₁ (endpointProjector v)).trace.re ∧
      (endpointProjector u * A₁ (endpointProjector v)).trace.re ≤ endpointAlpha ^ 2 := by
  rw [A₁_eq_weighted_pauli, trace_pauli_re, trace_projector_product, Complex.ofReal_re]
  simp only [trace_projector_conj]
  apply rankOne_arithmetic endpointBeta_nonneg endpointBeta_le_alpha endpointAlpha_add_beta
  · positivity
  · positivity
  · positivity
  · positivity
  · exact overlap_le_one u v hu hv
  · exact volume_overlap_le_one u v hu hv
  · simpa [hu, hv] using pauli_frame_overlap_le_two u v
  · simpa [hu, hv] using pauli_tail_overlap_le_two u v
  · have h := trace_twirl_re (endpointProjector u) (endpointProjector v)
    rw [endpoint_pauli_twirl, trace_endpointProjector, hv, one_pow, Complex.ofReal_one,
      mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, trace_endpointProjector,
      hu, one_pow, Complex.ofReal_one, smul_eq_mul, mul_one,
      trace_projector_product, Complex.ofReal_re] at h
    simpa only [trace_projector_conj, Complex.re_ofNat] using h.symm

/-- Every orthonormal basis resolves the identity into its rank-one projections. -/
theorem sum_endpointProjector (B : OrthonormalBasis (Fin 4) ℂ EndpointVector) :
    (∑ i, endpointProjector (B i)) = (1 : TwoMode) := by
  apply Matrix.toEuclideanLin.injective
  rw [map_sum, Matrix.toLpLin_one]
  ext x : 1
  simp only [LinearMap.sum_apply, LinearMap.id_apply]
  convert B.sum_repr' x using 1
  apply Finset.sum_congr rfl
  intro i _
  change WithLp.toLp 2
      (Matrix.vecMulVec (WithLp.ofLp (B i)) (star (WithLp.ofLp (B i))) *ᵥ WithLp.ofLp x) = _
  rw [Matrix.vecMulVec_mulVec, dotProduct_comm (star (WithLp.ofLp (B i))),
    ← EuclideanSpace.inner_eq_star_dotProduct]
  ext k
  change (B i).ofLp k * ⟪B i, x⟫_ℂ = ⟪B i, x⟫_ℂ * (B i).ofLp k
  exact mul_comm _ _

private theorem unitary_right_mul (A B : TwoMode) (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) :
    (A * B) * (A * B)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, mul_assoc A B, ← mul_assoc B Bᴴ, hB, one_mul, hA]

private theorem endpointU_unitary_right (j : Fin 4) : endpointU j * (endpointU j)ᴴ = 1 := by
  rw [(endpointU_hermitian j).eq, endpointU_sq]

theorem endpointTriple_unitary_right (j : Fin 4) :
    endpointTriple j * (endpointTriple j)ᴴ = 1 := by
  fin_cases j <;>
    exact unitary_right_mul _ _ (unitary_right_mul _ _ (endpointU_unitary_right _)
      (endpointU_unitary_right _)) (endpointU_unitary_right _)

theorem endpointVolume_unitary_right : endpointVolume * endpointVolumeᴴ = 1 :=
  unitary_right_mul _ _ (unitary_right_mul _ _
    (unitary_right_mul _ _ (endpointU_unitary_right 0) (endpointU_unitary_right 1))
    (endpointU_unitary_right 2)) (endpointU_unitary_right 3)

private theorem trace_readout_add (P X Y : TwoMode) :
    (P * (X + Y)).trace.re = (P * X).trace.re + (P * Y).trace.re := by
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

/-- The mixed rank bound for the projection onto the first two vectors of any
orthonormal basis. The testing unit vector can be in a different basis. -/
theorem A₁_rankOne_rankTwo_basis (u : EndpointVector) (hu : ‖u‖ = 1)
    (B : OrthonormalBasis (Fin 4) ℂ EndpointVector) :
    (endpointProjector u * A₁ (endpointProjector (B 0) + endpointProjector (B 1))).trace.re ≤
      endpointAlpha := by
  let P := endpointProjector u
  let Q := endpointProjector (B 0) + endpointProjector (B 1)
  let R := endpointProjector (B 2) + endpointProjector (B 3)
  have hn (i : Fin 4) : ‖B i‖ = 1 := B.orthonormal.1 i
  have hsum : Q + R = 1 := by
    have h := sum_endpointProjector B
    simp only [Fin.sum_univ_four] at h
    simpa [Q, R, add_assoc] using h
  have hQ : Q.trace = 2 := by
    norm_num [Q, Matrix.trace_add, trace_endpointProjector, hn]
  have conj_add (U : TwoMode) :
      (P * MatrixMap.conj U Q).trace.re =
        ‖⟪u, U.toEuclideanLin (B 0)⟫_ℂ‖ ^ 2 +
          ‖⟪u, U.toEuclideanLin (B 1)⟫_ℂ‖ ^ 2 := by
    simp only [P, Q, map_add, trace_readout_add, trace_projector_conj]
  have h₀ : (P * Q).trace.re ≤ 1 := by
    have h := B.sum_sq_norm_inner_left u
    rw [Fin.sum_univ_four, hu, one_pow] at h
    simp only [P, Q, trace_readout_add, trace_projector_product, Complex.ofReal_re]
    linarith only [h, sq_nonneg ‖⟪u, B 2⟫_ℂ‖, sq_nonneg ‖⟪u, B 3⟫_ℂ‖]
  have hhead : (P * Q).trace.re +
      (∑ j : Fin 4, (P * MatrixMap.conj (endpointU j) Q).trace.re) ≤ 4 := by
    have h₀ := pauli_frame_overlap_le_two u (B 0)
    have h₁ := pauli_frame_overlap_le_two u (B 1)
    simp only [hu, hn, one_pow, mul_one] at h₀ h₁
    simp only [conj_add, Finset.sum_add_distrib]
    simp only [P, Q, trace_readout_add, trace_projector_product, Complex.ofReal_re]
    linarith only [h₀, h₁]
  have htailR : (∑ j : Fin 4, (P * MatrixMap.conj (endpointTriple j) R).trace.re) +
        (P * MatrixMap.conj endpointVolume R).trace.re ≤ 4 := by
    have h₂ := pauli_tail_overlap_le_two u (B 2)
    have h₃ := pauli_tail_overlap_le_two u (B 3)
    simp only [hu, hn, one_pow, mul_one] at h₂ h₃
    simp only [P, R, map_add, trace_readout_add, trace_projector_conj, Finset.sum_add_distrib]
    linarith only [h₂, h₃]
  have hU (U : TwoMode) (hU : U * Uᴴ = 1) :
      (P * MatrixMap.conj U Q).trace.re + (P * MatrixMap.conj U R).trace.re = 1 := by
    rw [← trace_readout_add, ← map_add, hsum, MatrixMap.conj_apply, mul_one, hU, mul_one]
    simp [P, trace_endpointProjector, hu]
  have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 4)) = Finset.univ)
    (fun j _ => hU (endpointTriple j) (endpointTriple_unitary_right j))
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat] at hs
  have htailQ :
      1 ≤ (∑ j : Fin 4, (P * MatrixMap.conj (endpointTriple j) Q).trace.re) +
        (P * MatrixMap.conj endpointVolume Q).trace.re :=
    by linarith only [htailR, hs, hU _ endpointVolume_unitary_right]
  have htotal := trace_twirl_re P Q
  rw [endpoint_pauli_twirl, hQ, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    smul_eq_mul] at htotal
  have htrace : P.trace = 1 := by simp [P, trace_endpointProjector, hu]
  rw [htrace, mul_one] at htotal
  norm_num only [Complex.re_ofNat, Nat.reduceMul] at htotal
  -- The five coefficients of the Pauli trace, ordered by the number of generators.
  let f : ℕ → ℝ := fun
    | 0 => (P * Q).trace.re
    | 1 => ∑ j : Fin 4, (P * MatrixMap.conj (endpointU j) Q).trace.re
    | 2 => ∑ j : Fin 6, (P * MatrixMap.conj (endpointPair j) Q).trace.re
    | 3 => ∑ j : Fin 4, (P * MatrixMap.conj (endpointTriple j) Q).trace.re
    | 4 => (P * MatrixMap.conj endpointVolume Q).trace.re
    | _ => 0
  let c : ℕ → ℝ := fun
    | 0 => 1
    | 1 | 2 => 3
    | 3 => 1
    | _ => 0
  let w (i : ℕ) : ℝ := endpointAlpha ^ (4 - i) * endpointBeta ^ i
  change f 0 ≤ 1 at h₀
  change f 0 + f 1 ≤ 4 at hhead
  change 1 ≤ f 3 + f 4 at htailQ
  change 8 = f 0 + f 1 + f 2 + f 3 + f 4 at htotal
  have hf₄ : 0 ≤ f 4 := by
    change 0 ≤ (P * MatrixMap.conj endpointVolume Q).trace.re
    rw [conj_add]
    positivity
  have hprefix (k : ℕ) (hk : k ≤ 5) :
      (∑ i ∈ Finset.range k, f i) ≤ ∑ i ∈ Finset.range k, c i := by
    interval_cases k <;> norm_num [Finset.sum_range_succ, c]
    · exact h₀
    · exact hhead
    · linarith only [htailQ, htotal]
    · linarith only [hf₄, htotal]
    · exact htotal.symm.le
  have hα := endpointBeta_nonneg.trans endpointBeta_le_alpha
  have hw₀ : 0 ≤ w := by
    intro i
    exact mul_nonneg (pow_nonneg hα _) (pow_nonneg endpointBeta_nonneg _)
  have hw : AntitoneOn w (Set.Iio 5) := by
    intro i _hi j hj hij
    have hj' : j < 5 := Set.mem_Iio.mp hj
    have hβexp : i + (j - i) = j := by omega
    have hαexp : (4 - j) + (j - i) = 4 - i := by omega
    calc
      w j = (endpointAlpha ^ (4 - j) * endpointBeta ^ i) * endpointBeta ^ (j - i) := by
        dsimp only [w]
        rw [mul_assoc, ← pow_add, hβexp]
      _ ≤ (endpointAlpha ^ (4 - j) * endpointBeta ^ i) * endpointAlpha ^ (j - i) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ endpointBeta_nonneg endpointBeta_le_alpha _)
          (mul_nonneg (pow_nonneg hα _) (pow_nonneg endpointBeta_nonneg _))
      _ = w i := by
        dsimp only [w]
        rw [mul_right_comm, ← pow_add, hαexp]
  change (P * A₁ Q).trace.re ≤ endpointAlpha
  calc
    (P * A₁ Q).trace.re = ∑ i ∈ Finset.range 5, f i * w i := by
      rw [A₁_eq_weighted_pauli, trace_pauli_re]
      norm_num [Finset.sum_range_succ, f, w] <;> ring
    _ ≤ ∑ i ∈ Finset.range 5, c i * w i :=
      Finset.sum_mul_le_sum_mul_of_sum_range_le hprefix hw₀ hw
    _ = endpointAlpha * (endpointAlpha + endpointBeta) ^ 3 := by
      norm_num [Finset.sum_range_succ, c, w] <;> ring
    _ = endpointAlpha := by rw [endpointAlpha_add_beta, one_pow, mul_one]

#print axioms A₁_rankOne_rankOne
#print axioms A₁_rankOne_rankTwo_basis

end WuRankOneEndpointFloor
