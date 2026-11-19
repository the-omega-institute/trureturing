/- GID: D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointPrefixMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordered spectrum of the signed map is majorized by classical two-bit noise on the input spectrum. -/

import D5.S3.Quantum.Semigroups.WuEndpointProjectionBounds
import Mathlib.Analysis.Matrix.Spectrum

/-! Spectral prefixes for the signed two-mode endpoint. -/

noncomputable section

open Matrix BigOperators
open scoped InnerProductSpace Kronecker ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation (pauli_trace_pair)

namespace WuRankOneEndpointFloor

private theorem pauliWord_trace_orthogonal (p q r s : Pauli) :
    (pauliWord p q * pauliWord r s).trace =
      if p = r ∧ q = s then 4 else 0 := by
  unfold pauliWord
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, pauli_trace_pair, pauli_trace_pair]
  by_cases hp : p = r <;> by_cases hq : q = s <;> norm_num [hp, hq]

private def productTrace (P : TwoMode) : TwoMode →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap Mode ℂ ℂ).comp (LinearMap.mulLeft ℂ P)

/-- Symmetry of the trace pairing for the actual channel. -/
theorem A₁_trace_pair_swap (P Q : TwoMode) : (P * A₁ Q).trace = (Q * A₁ P).trace := by
  have h (r s : Pauli) :
      (productTrace (pauliWord r s)).comp A₁ = productTrace (A₁ (pauliWord r s)) := by
    apply endpoint_map_eq_on_pauli
    intro p q
    change (pauliWord r s * A₁ (pauliWord p q)).trace =
      (A₁ (pauliWord r s) * pauliWord p q).trace
    rw [A₁_pauliWord, A₁_pauliWord, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_smul, pauliWord_trace_orthogonal]
    by_cases he : r = p ∧ s = q
    · obtain ⟨rfl, rfl⟩ := he
      rfl
    · simp [he]
  have H : (productTrace Q).comp A₁ = productTrace (A₁ Q) := by
    apply endpoint_map_eq_on_pauli
    intro p q
    change (Q * A₁ (pauliWord p q)).trace = (A₁ Q * pauliWord p q).trace
    have hh := DFunLike.congr_fun (h p q) Q
    change (pauliWord p q * A₁ Q).trace = (A₁ (pauliWord p q) * Q).trace at hh
    calc
      _ = (A₁ (pauliWord p q) * Q).trace := Matrix.trace_mul_comm _ _
      _ = (pauliWord p q * A₁ Q).trace := hh.symm
      _ = _ := Matrix.trace_mul_comm _ _
  have h' := DFunLike.congr_fun H P
  change (Q * A₁ P).trace = (A₁ Q * P).trace at h'
  exact (Matrix.trace_mul_comm _ _).trans h'.symm

theorem A₁_one : A₁ (1 : TwoMode) = 1 := by
  have hI : pauliWord .I .I = 1 := Matrix.one_kronecker_one
  simpa [hI, cliffordDegree] using A₁_pauliWord .I .I

theorem A₁_trace (X : TwoMode) : (A₁ X).trace = X.trace := by
  simpa only [one_mul, A₁_one, mul_one] using A₁_trace_pair_swap 1 X

theorem A₁_isHermitian (X : TwoMode) (hX : X.IsHermitian) : (A₁ X).IsHermitian := by
  have h (U : TwoMode) : (U * X * Uᴴ)ᴴ = U * X * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hX.eq, mul_assoc]
  change (A₁ X)ᴴ = A₁ X
  rw [A₁_eq_weighted_pauli]
  simp only [endpointConjugationSum, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.sum_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Complex.star_def, Complex.conj_ofReal, MatrixMap.conj_apply, hX.eq, h]

abbrev EndpointBasis := OrthonormalBasis (Fin 4) ℂ EndpointVector

/-- The three proper-prefix projectors in a chosen orthonormal basis. -/
def endpointPrefix (B : EndpointBasis) (k : Fin 3) : TwoMode :=
  ![endpointProjector (B 0),
    endpointProjector (B 0) + endpointProjector (B 1),
    endpointProjector (B 0) + endpointProjector (B 1) + endpointProjector (B 2)] k

private def test (P Q : TwoMode) : ℝ := (P * A₁ Q).trace.re

private theorem test_swap (P Q : TwoMode) : test P Q = test Q P :=
  congrArg Complex.re (A₁_trace_pair_swap P Q)

private theorem test_add_left (P Q R : TwoMode) : test (P + Q) R = test P R + test Q R := by
  simp only [test, Matrix.add_mul, Matrix.trace_add, Complex.add_re]

private theorem test_add_right (P Q R : TwoMode) : test P (Q + R) = test P Q + test P R := by
  simp only [test, map_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

private theorem test_one (P : TwoMode) : test P 1 = P.trace.re := by
  simp [test, A₁_one]

private theorem test_one_left (P : TwoMode) : test 1 P = P.trace.re := by
  rw [test_swap, test_one]

private theorem test_sub_right (P Q R : TwoMode) : test P (Q - R) = test P Q - test P R := by
  simp only [test, map_sub, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

private theorem test_sub_left (P Q R : TwoMode) : test (P - Q) R = test P R - test Q R := by
  simp only [test, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

private theorem test_smul_right (P Q : TwoMode) (r : ℝ) :
    test P ((r : ℂ) • Q) = r * test P Q := by
  simp [test, Matrix.trace_smul, Complex.re_ofReal_mul]

private theorem prefix0 (B : EndpointBasis) : endpointPrefix B 0 = endpointProjector (B 0) := rfl
private theorem prefix1 (B : EndpointBasis) :
    endpointPrefix B 1 = endpointProjector (B 0) + endpointProjector (B 1) := rfl
private theorem prefix2 (B : EndpointBasis) : endpointPrefix B 2 = 1 - endpointProjector (B 3) := by
  apply eq_sub_of_add_eq
  change endpointProjector (B 0) + endpointProjector (B 1) +
    endpointProjector (B 2) + endpointProjector (B 3) = 1
  simpa only [Fin.sum_univ_four] using sum_endpointProjector B

private theorem test_single_single (B C : EndpointBasis) (i j : Fin 4) :
    endpointBeta ^ 2 ≤ test (endpointProjector (B i)) (endpointProjector (C j)) ∧
      test (endpointProjector (B i)) (endpointProjector (C j)) ≤ endpointAlpha ^ 2 :=
  A₁_rankOne_rankOne _ _ (B.orthonormal.1 i) (C.orthonormal.1 j)

private theorem test_single_pair (B C : EndpointBasis) (i : Fin 4) :
    test (endpointProjector (B i)) (endpointPrefix C 1) ≤ endpointAlpha :=
  A₁_rankOne_rankTwo_basis _ (B.orthonormal.1 i) C

private theorem trace_basis_projector (B : EndpointBasis) (i : Fin 4) :
    (endpointProjector (B i)).trace.re = 1 := by
  rw [trace_endpointProjector, Complex.ofReal_re, B.orthonormal.1 i, one_pow]

private theorem trace_basis_pair (B : EndpointBasis) : (endpointPrefix B 1).trace.re = 2 := by
  rw [prefix1, Matrix.trace_add, Complex.add_re, trace_basis_projector, trace_basis_projector]
  norm_num

/-- The classical two-bit noise matrix, with the order 00, 01, 10, 11. -/
def endpointClassical (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let a := endpointAlpha
  let b := endpointBeta
  ![a^2*x 0 + a*b*x 1 + a*b*x 2 + b^2*x 3,
    a*b*x 0 + a^2*x 1 + b^2*x 2 + a*b*x 3,
    a*b*x 0 + b^2*x 1 + a^2*x 2 + a*b*x 3,
    b^2*x 0 + a*b*x 1 + a*b*x 2 + a^2*x 3]

private def prefixBound (k l : Fin 3) : ℝ :=
  let a := endpointAlpha
  let b := endpointBeta
  ![![a^2, a, 1-b^2], ![a, 2*a, 1+a], ![1-b^2, 1+a, 2+a^2]] k l

private def oppositeBasis (B : EndpointBasis) : EndpointBasis :=
  B.reindex (Equiv.addRight (2 : Fin 4))

private theorem opposite_pair (B : EndpointBasis) :
    endpointPrefix (oppositeBasis B) 1 + endpointPrefix B 1 = 1 := by
  have h0 : (Equiv.addRight (2 : Fin 4)).symm 0 = 2 := by decide
  have h1 : (Equiv.addRight (2 : Fin 4)).symm 1 = 3 := by decide
  rw [prefix1, prefix1, oppositeBasis, OrthonormalBasis.reindex_apply,
    OrthonormalBasis.reindex_apply, h0, h1]
  simpa [Fin.sum_univ_four, add_assoc, add_comm, add_left_comm] using sum_endpointProjector B

private theorem prefix_test_bound (B C : EndpointBasis) (k l : Fin 3) :
    test (endpointPrefix B k) (endpointPrefix C l) ≤ prefixBound k l := by
  fin_cases k <;> fin_cases l
  · exact (test_single_single B C 0 0).2
  · exact test_single_pair B C 0
  · change test (endpointPrefix B 0) (endpointPrefix C 2) ≤ 1 - endpointBeta ^ 2
    rw [prefix0, prefix2, test_sub_right, test_one, trace_basis_projector]
    exact sub_le_sub_left (test_single_single B C 0 3).1 1
  · change test (endpointPrefix B 1) (endpointPrefix C 0) ≤ endpointAlpha
    rw [test_swap]
    exact test_single_pair C B 0
  · change test (endpointPrefix B 1) (endpointPrefix C 1) ≤ 2 * endpointAlpha
    rw [prefix1 B, test_add_left]
    linarith only [test_single_pair B C 0, test_single_pair B C 1]
  · change test (endpointPrefix B 1) (endpointPrefix C 2) ≤ 1 + endpointAlpha
    rw [prefix2, test_sub_right, test_one, trace_basis_pair, test_swap]
    have ht := test_add_right (endpointProjector (C 3))
      (endpointPrefix (oppositeBasis B) 1) (endpointPrefix B 1)
    rw [opposite_pair, test_one, trace_basis_projector] at ht
    linarith only [ht, test_single_pair C (oppositeBasis B) 3]
  · change test (endpointPrefix B 2) (endpointPrefix C 0) ≤ 1 - endpointBeta ^ 2
    rw [test_swap, prefix0, prefix2, test_sub_right, test_one, trace_basis_projector]
    exact sub_le_sub_left (test_single_single C B 0 3).1 1
  · change test (endpointPrefix B 2) (endpointPrefix C 1) ≤ 1 + endpointAlpha
    rw [prefix2, test_sub_left, test_one_left, trace_basis_pair]
    have ht := test_add_right (endpointProjector (B 3))
      (endpointPrefix (oppositeBasis C) 1) (endpointPrefix C 1)
    rw [opposite_pair, test_one, trace_basis_projector] at ht
    linarith only [ht, test_single_pair B (oppositeBasis C) 3]
  · change test (endpointPrefix B 2) (endpointPrefix C 2) ≤ 2 + endpointAlpha ^ 2
    simp only [prefix2, test_sub_left, test_sub_right, test_one_left, test_one,
      Matrix.trace_sub, Complex.sub_re, trace_basis_projector]
    have h1 : ((1 : TwoMode).trace).re = 4 := by norm_num [Matrix.trace_one]
    linarith only [h1, (test_single_single B C 3 3).2]

/-- The first k+1 entries, for the three proper prefixes of a four-vector. -/
def endpointPrefixSum (x : Fin 4 → ℝ) (k : Fin 3) : ℝ :=
  ![x 0, x 0 + x 1, x 0 + x 1 + x 2] k

private def spectralSum (B : EndpointBasis) (x : Fin 4 → ℝ) : TwoMode :=
  ∑ i, (x i : ℂ) • endpointProjector (B i)

private theorem spectralSum_prefix (B : EndpointBasis) (x : Fin 4 → ℝ) :
    spectralSum B x =
      (x 3 : ℂ) • (1 : TwoMode) +
        ((x 0 - x 1 : ℝ) : ℂ) • endpointPrefix B 0 +
        ((x 1 - x 2 : ℝ) : ℂ) • endpointPrefix B 1 +
        ((x 2 - x 3 : ℝ) : ℂ) • endpointPrefix B 2 := by
  rw [← sum_endpointProjector B]
  simp [spectralSum, endpointPrefix, Fin.sum_univ_four]
  module

private theorem prefix_trace (B : EndpointBasis) (k : Fin 3) :
    (endpointPrefix B k).trace.re = ![(1 : ℝ), 2, 3] k := by
  fin_cases k <;> norm_num [endpointPrefix, Matrix.trace_add, Complex.add_re, trace_basis_projector]

private theorem classical_prefix (x : Fin 4 → ℝ) (k : Fin 3) :
    endpointPrefixSum (endpointClassical x) k =
      ![(1 : ℝ), 2, 3] k * x 3 + (x 0 - x 1) * prefixBound k 0 +
      (x 1 - x 2) * prefixBound k 1 + (x 2 - x 3) * prefixBound k 2 := by
  have hb : endpointBeta = 1 - endpointAlpha := by linarith [endpointAlpha_add_beta]
  fin_cases k <;> simp [endpointPrefixSum, endpointClassical, prefixBound] <;> rw [hb] <;> ring

theorem A₁_prefix_basis_bound (B C : EndpointBasis) (x : Fin 4 → ℝ)
    (hx : Antitone x) (k : Fin 3) :
    test (endpointPrefix B k) (spectralSum C x) ≤ endpointPrefixSum (endpointClassical x) k := by
  rw [spectralSum_prefix, classical_prefix]
  simp only [test_add_right, test_smul_right, test_one, prefix_trace]
  have h01 : 0 ≤ x 0 - x 1 := sub_nonneg.mpr (hx (by decide : (0 : Fin 4) ≤ 1))
  have h12 : 0 ≤ x 1 - x 2 := sub_nonneg.mpr (hx (by decide : (1 : Fin 4) ≤ 2))
  have h23 : 0 ≤ x 2 - x 3 := sub_nonneg.mpr (hx (by decide : (2 : Fin 4) ≤ 3))
  exact add_le_add
    (add_le_add
      (add_le_add (le_of_eq (mul_comm _ _))
        (mul_le_mul_of_nonneg_left (prefix_test_bound B C k 0) h01))
      (mul_le_mul_of_nonneg_left (prefix_test_bound B C k 1) h12))
    (mul_le_mul_of_nonneg_left (prefix_test_bound B C k 2) h23)

private abbrev spectrumIndex : Fin 4 ≃ Mode :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card Mode))

private def orderedBasis {X : TwoMode} (hX : X.IsHermitian) : EndpointBasis :=
  hX.eigenvectorBasis.reindex spectrumIndex.symm

private theorem ordered_basis_eval {X : TwoMode} (hX : X.IsHermitian) (i : Fin 4) :
    X.toEuclideanLin (orderedBasis hX i) =
      (hX.eigenvalues₀ i : ℂ) • orderedBasis hX i := by
  apply WithLp.ofLp_injective
  have he : hX.eigenvalues (spectrumIndex i) = hX.eigenvalues₀ i := by
    change hX.eigenvalues₀ (spectrumIndex.symm (spectrumIndex i)) = _
    rw [Equiv.symm_apply_apply]
  have h := hX.mulVec_eigenvectorBasis (spectrumIndex i)
  rw [he] at h
  simpa [orderedBasis, OrthonormalBasis.reindex_apply, Matrix.toLpLin_apply] using h

private theorem projector_toEuclideanLin (u v : EndpointVector) :
    (endpointProjector u).toEuclideanLin v = ⟪u, v⟫_ℂ • u := by
  change WithLp.toLp 2
    (Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)) *ᵥ WithLp.ofLp v) = _
  rw [Matrix.vecMulVec_mulVec, dotProduct_comm (star (WithLp.ofLp u)),
    ← EuclideanSpace.inner_eq_star_dotProduct]
  ext i
  change u.ofLp i * ⟪u, v⟫_ℂ = ⟪u, v⟫_ℂ * u.ofLp i
  exact mul_comm _ _

private theorem actual_spectralSum {X : TwoMode} (hX : X.IsHermitian) :
    X = spectralSum (orderedBasis hX) hX.eigenvalues₀ := by
  unfold spectralSum
  apply Matrix.toEuclideanLin.injective
  rw [map_sum]
  ext v : 1
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, projector_toEuclideanLin]
  conv_lhs => arg 2; rw [← (orderedBasis hX).sum_repr' v]
  simp only [map_sum, map_smul, ordered_basis_eval, smul_smul, mul_comm]

private theorem trace_prefix_eigen {X : TwoMode} (hX : X.IsHermitian) (k : Fin 3) :
    (endpointPrefix (orderedBasis hX) k * X).trace.re = endpointPrefixSum hX.eigenvalues₀ k := by
  have hp (i : Fin 4) : (endpointProjector (orderedBasis hX i) * X).trace.re = hX.eigenvalues₀ i := by
    rw [trace_endpointProjector_mul, ordered_basis_eval, inner_smul_right, inner_self_eq_norm_sq_to_K,
      (orderedBasis hX).orthonormal.1 i]
    simp
  fin_cases k <;> simp [endpointPrefix, endpointPrefixSum, Matrix.add_mul,
    Matrix.trace_add, Complex.add_re, hp]

/-- Proper-prefix spectral comparisons for every Hermitian input on the actual signed channel. -/
theorem A₁_spectral_prefix (X : TwoMode) (hX : X.IsHermitian) (k : Fin 3) :
    endpointPrefixSum (A₁_isHermitian X hX).eigenvalues₀ k ≤
      endpointPrefixSum (endpointClassical hX.eigenvalues₀) k := by
  let hY := A₁_isHermitian X hX
  have h := A₁_prefix_basis_bound (orderedBasis hY) (orderedBasis hX) hX.eigenvalues₀
    hX.eigenvalues₀_antitone k
  rw [← actual_spectralSum hX] at h
  rw [← trace_prefix_eigen hY k]
  exact h

theorem A₁_spectral_total (X : TwoMode) (hX : X.IsHermitian) :
    (∑ i : Fin 4, (A₁_isHermitian X hX).eigenvalues₀ i) =
      ∑ i : Fin 4, endpointClassical hX.eigenvalues₀ i := by
  have trace_eq {Y : TwoMode} (hY : Y.IsHermitian) :
      Y.trace.re = ∑ i : Fin 4, hY.eigenvalues₀ i := by
    conv_lhs => rw [actual_spectralSum hY]
    simp [spectralSum, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
      trace_endpointProjector, (orderedBasis hY).orthonormal.1]
  rw [← trace_eq (A₁_isHermitian X hX), A₁_trace, trace_eq hX]
  have hb : endpointBeta = 1 - endpointAlpha := by linarith [endpointAlpha_add_beta]
  change (∑ i : Fin 4, hX.eigenvalues₀ i) = _
  have hfin := Fin.sum_univ_four (fun i : Fin 4 => hX.eigenvalues₀ i)
  rw [hfin]
  simp [Fin.sum_univ_four, endpointClassical, hb] <;> ring

theorem endpointClassical_antitone (x : Fin 4 → ℝ) (hx : Antitone x) :
    Antitone (endpointClassical x) := by
  have ha := endpointBeta_nonneg.trans endpointBeta_le_alpha
  have hb := endpointBeta_nonneg
  have hd := sub_nonneg.mpr endpointBeta_le_alpha
  have h01 := sub_nonneg.mpr (hx (by decide : (0 : Fin 4) ≤ 1))
  have h12 := sub_nonneg.mpr (hx (by decide : (1 : Fin 4) ≤ 2))
  have h23 := sub_nonneg.mpr (hx (by decide : (2 : Fin 4) ≤ 3))
  have h01' : endpointClassical x 1 ≤ endpointClassical x 0 := by
    apply sub_nonneg.mp
    have h :
        endpointClassical x 0 - endpointClassical x 1 =
          (endpointAlpha - endpointBeta) *
            (endpointAlpha * (x 0 - x 1) + endpointBeta * (x 2 - x 3)) := by
      simp [endpointClassical]; ring
    rw [h]
    positivity
  have h12' : endpointClassical x 2 ≤ endpointClassical x 1 := by
    apply sub_nonneg.mp
    have h :
        endpointClassical x 1 - endpointClassical x 2 =
          (endpointAlpha - endpointBeta) * (endpointAlpha + endpointBeta) * (x 1 - x 2) := by
      simp [endpointClassical]; ring
    rw [h]
    positivity
  have h23' : endpointClassical x 3 ≤ endpointClassical x 2 := by
    apply sub_nonneg.mp
    have h :
        endpointClassical x 2 - endpointClassical x 3 =
          (endpointAlpha - endpointBeta) *
            (endpointBeta * (x 0 - x 1) + endpointAlpha * (x 2 - x 3)) := by
      simp [endpointClassical]; ring
    rw [h]
    positivity
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢ <;>
    first | exact le_rfl | cases (show False by omega) | linarith only [h01', h12', h23']

/-- The actual signed channel's ordered eigenvalues are majorized by the classical
two-bit convolution of the ordered input eigenvalues. -/
theorem A₁_spectral_majorization (X : TwoMode) (hX : X.IsHermitian) :
    Antitone (endpointClassical hX.eigenvalues₀) ∧
    (∀ k : Fin 3,
      endpointPrefixSum (A₁_isHermitian X hX).eigenvalues₀ k ≤
        endpointPrefixSum (endpointClassical hX.eigenvalues₀) k) ∧
    (∑ i : Fin 4, (A₁_isHermitian X hX).eigenvalues₀ i) =
      ∑ i : Fin 4, endpointClassical hX.eigenvalues₀ i :=
  ⟨endpointClassical_antitone _ hX.eigenvalues₀_antitone, A₁_spectral_prefix X hX,
    A₁_spectral_total X hX⟩

#print axioms A₁_spectral_majorization
#print axioms A₁_spectral_prefix
#print axioms A₁_spectral_total
#print axioms endpointClassical_antitone

#print axioms A₁_trace_pair_swap
#print axioms prefix_test_bound

end WuRankOneEndpointFloor
