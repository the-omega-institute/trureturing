/- GID: D5/S3/Estimation/CenteredTopEigenvectorObstruction
   generality: G
   mirror-B: D5/B/S3/Estimation/CenteredTopEigenvectorObstruction
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: A top eigenvector of weight at most one half bounds the centered energy and the half trace of a symmetric matrix. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#153)
escape_witness: top_pair (an arbitrary unit eigenvector of the largest eigenvalue with weight at
  most one half yields two distinct eigenbasis indices whose eigenvalues bound twice the
  Rayleigh quotient: either the largest eigenvalue is repeated, or the eigenvector is a signed
  basis vector and the weight transfers to it).
proof_shape:
  top_pair: content; consumer: result.
  centered_trace: bind-only (frozen trace and Frobenius identities plus expansion); consumer:
    result.
  result: content.
Direct frozen dependencies: D5/S3/Estimation/CorrelationTopEigenvectorWeight
  (two_point_energy, top_pair_of_weights, eigenbasis_rayleigh),
  D5/S3/Weil/ZetaLinear/PosIndex (RHLinalg.rtrace_eq_sum_eigenvalues,
  RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues).
Search record (§3.1): the two-point energy inequality, the weight-pair selection and the
  eigenbasis Rayleigh expansion come from CorrelationTopEigenvectorWeight; Mathlib supplies the spectral theorem
  (Matrix.IsHermitian.eigenvectorBasis) and isSymmetric_toEuclideanLin_iff. The frozen
  result there concerns correlation matrices and the normalized diagonal vector only.
-/

import D5.S3.Estimation.CorrelationTopEigenvectorWeight

/-! # The centered top-eigenvector obstruction for symmetric matrices

Let `H` be a real symmetric `n × n` matrix, `u` a unit vector, `τ = tr H / n` and
`r = uᵀ H u - τ`. If some unit eigenvector `v` for the largest eigenvalue has
`⟪u, v⟫² ≤ 1/2`, then two distinct eigenvalues satisfy `2 uᵀ H u ≤ λ_i + λ_j`. For `r ≥ 0`
this forces `2n r² ≤ (n - 2) tr ((H - τ I)²)`, and for positive semidefinite `H` it forces
`uᵀ H u ≤ tr H / 2`.
-/

set_option autoImplicit false

open Matrix Finset
open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Estimation.CenteredTopEigenvectorObstruction

open D5.S3.Estimation.CorrelationTopEigenvectorWeight

noncomputable section

/-- A unit top eigenvector of weight at most one half relative to `u` yields two distinct
eigenbasis indices whose eigenvalues bound twice the Rayleigh quotient of `u`. -/
private lemma top_pair {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv1 : ‖v‖ = 1) (l : ℝ)
    (hv : H.toEuclideanLin v = l • v)
    (htop : ∀ (m : ℝ) (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → H.toEuclideanLin x = m • x →
      m ≤ l)
    (hw : ⟪u, v⟫ ^ 2 ≤ 1 / 2) :
    ∃ i j, i ≠ j ∧
      2 * ⟪u, H.toEuclideanLin u⟫ ≤ hH.eigenvalues i + hH.eigenvalues j := by
  classical
  set b := hH.eigenvectorBasis with hb
  set e := hH.eigenvalues with he
  have hbv : ∀ j, H.toEuclideanLin (b j) = e j • b j := fun j =>
    (WithLp.equiv 2 _).injective (hH.mulVec_eigenvectorBasis j)
  have hsymm := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH)
  have hle : ∀ j, e j ≤ l := fun j => htop (e j) (b j) (b.orthonormal.ne_zero j) (hbv j)
  have hcoef : ∀ j, ⟪b j, v⟫ ≠ 0 → e j = l := by
    intro j hj
    have h1 : ⟪H.toEuclideanLin (b j), v⟫ = ⟪b j, H.toEuclideanLin v⟫ := hsymm (b j) v
    rw [hbv, hv, inner_smul_left, inner_smul_right] at h1
    simp only [conj_trivial] at h1
    exact mul_right_cancel₀ hj h1
  have hwsum : ∑ j, ⟪b j, u⟫ ^ 2 = 1 := by rw [b.sum_sq_inner_right, hu, one_pow]
  have hcsum : ∑ j, ⟪b j, v⟫ ^ 2 = 1 := by rw [b.sum_sq_inner_right, hv1, one_pow]
  have hray : ∑ j, e j * ⟪b j, u⟫ ^ 2 = ⟪u, H.toEuclideanLin u⟫ :=
    eigenbasis_rayleigh H b e (hH.mulVec_eigenvectorBasis) u
  obtain ⟨i, hi⟩ : ∃ i, ⟪b i, v⟫ ≠ 0 := by
    by_contra h
    push Not at h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
      at hcsum
    exact zero_ne_one hcsum
  have hei : e i = l := hcoef i hi
  have hrayle : ⟪u, H.toEuclideanLin u⟫ ≤ l := by
    rw [← hray]
    calc ∑ j, e j * ⟪b j, u⟫ ^ 2 ≤ ∑ j, l * ⟪b j, u⟫ ^ 2 :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (sq_nonneg _)
      _ = l := by rw [← mul_sum, hwsum, mul_one]
  by_cases hpair : ∃ j, j ≠ i ∧ e j = l
  · obtain ⟨j, hji, hej⟩ := hpair
    exact ⟨i, j, hji.symm, by rw [hei, hej]; linarith⟩
  · push Not at hpair
    have hzero : ∀ j, j ≠ i → ⟪b j, v⟫ = 0 := fun j hji => by
      by_contra h
      exact hpair j hji (hcoef j h)
    have hci : ⟪b i, v⟫ ^ 2 = 1 := by
      rw [← hcsum, sum_eq_single i (fun j _ hji => by rw [hzero j hji]; norm_num)
        (by simp)]
    have huv : ⟪u, v⟫ = ⟪u, b i⟫ * ⟪b i, v⟫ := by
      rw [← b.sum_inner_mul_inner u v, sum_eq_single i
        (fun j _ hji => by rw [hzero j hji, mul_zero]) (by simp)]
    have hwi : ⟪b i, u⟫ ^ 2 ≤ 1 / 2 := by
      rw [huv, mul_pow, hci, mul_one, real_inner_comm] at hw
      exact hw
    obtain ⟨j, hji, hj⟩ := top_pair_of_weights e (fun k => ⟪b k, u⟫ ^ 2)
      (fun k => sq_nonneg _) hwsum i (fun k => hei ▸ hle k) hwi
    exact ⟨i, j, hji.symm, by rw [← hray]; exact hj⟩

/-- `tr ((H - τ I)²)` is the sum of the squared shifted eigenvalues. -/
private lemma centered_trace {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (τ : ℝ) :
    ((H - τ • (1 : Matrix (Fin n) (Fin n) ℝ)) * (H - τ • 1)).trace =
      ∑ k, (hH.eigenvalues k - τ) ^ 2 := by
  have hf := RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hH
  have ht := RHLinalg.rtrace_eq_sum_eigenvalues hH
  simp only [RHLinalg.frobSq, RHLinalg.rtrace, RCLike.re_to_real, hH.eq] at hf ht
  have hexp : (H - τ • (1 : Matrix (Fin n) (Fin n) ℝ)) * (H - τ • 1) =
      H * H - (2 * τ) • H + (τ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  rw [hexp, trace_add, trace_sub, trace_smul, trace_smul, trace_one, hf, ht]
  simp only [smul_eq_mul, Fintype.card_fin, sub_sq, sum_add_distrib, sum_sub_distrib,
    sum_const, card_univ, nsmul_eq_mul, mul_sum]
  ring_nf

/-- For real symmetric `H`, a unit vector `u` and a unit eigenvector `v` of the largest
eigenvalue with `⟪u, v⟫² ≤ 1/2`, put `τ = tr H / n` and `r = uᵀ H u - τ`. If `r ≥ 0` then
`2n r² ≤ (n - 2) tr ((H - τ I)²)`; if `H` is positive semidefinite then `uᵀ H u ≤ tr H / 2`. -/
theorem result {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv1 : ‖v‖ = 1) (l : ℝ)
    (hv : H.toEuclideanLin v = l • v)
    (htop : ∀ (m : ℝ) (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → H.toEuclideanLin x = m • x →
      m ≤ l)
    (hw : ⟪u, v⟫ ^ 2 ≤ 1 / 2) :
    (0 ≤ ⟪u, H.toEuclideanLin u⟫ - H.trace / n →
      2 * n * (⟪u, H.toEuclideanLin u⟫ - H.trace / n) ^ 2 ≤
        (n - 2) * ((H - (H.trace / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) *
          (H - (H.trace / n) • 1)).trace) ∧
    (H.PosSemidef → ⟪u, H.toEuclideanLin u⟫ ≤ H.trace / 2) := by
  classical
  obtain ⟨i, j, hij, hpair⟩ := top_pair H hH u v hu hv1 l hv htop hw
  set e := hH.eigenvalues with he
  have htr : H.trace = ∑ k, e k := by
    have ht := RHLinalg.rtrace_eq_sum_eigenvalues hH
    simpa only [RHLinalg.rtrace, RCLike.re_to_real] using ht
  refine ⟨fun hr => ?_, fun hpsd => ?_⟩
  · set τ := H.trace / n with hτ
    set r := ⟪u, H.toEuclideanLin u⟫ - τ with hr'
    rw [centered_trace H hH τ]
    have hsum2 : 2 * r ≤ (e i - τ) + (e j - τ) := by rw [hr']; linarith
    rcases Nat.lt_or_ge n 3 with hn | hn
    · have hn2 : n = 2 := by
        have h2 : 2 ≤ n := by
          rcases Nat.lt_or_ge n 2 with h | h
          · exfalso
            apply hij
            ext
            omega
          · exact h
        omega
      subst hn2
      have hτ2 : τ = (e i + e j) / 2 := by
        rw [hτ, htr]
        fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_two, add_comm]
      have hr0 : r = 0 := by rw [hτ2] at hsum2; linarith
      rw [hr0]
      simp
    · have hcent : ∑ k, (e k - τ) = 0 := by
        rw [sum_sub_distrib, ← htr, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hτ]
        have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
        have : (n : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      have henergy := two_point_energy hn (fun k => e k - τ) hcent i j hij
      have hsq : (2 * r) ^ 2 ≤ ((e i - τ) + (e j - τ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hsum2 2
      nlinarith [henergy, hsq]
  · have hnn : ∀ k, 0 ≤ e k := hpsd.eigenvalues_nonneg
    have hsub : e i + e j ≤ ∑ k, e k := by
      have h := sum_le_sum_of_subset_of_nonneg (subset_univ ({i, j} : Finset (Fin n)))
        (fun k _ _ => hnn k)
      rwa [sum_pair hij] at h
    rw [htr]
    linarith

end

end D5.S3.Estimation.CenteredTopEigenvectorObstruction
