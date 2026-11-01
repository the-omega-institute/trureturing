/- GID: D5/S3/Estimation/CorrelationTopEigenvectorWeight
   generality: G
   mirror-B: D5/B/S3/Estimation/CorrelationTopEigenvectorWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The remaining correlation domain admits the weight gap exactly above sigma=c. -/

import D5.S3.Estimation.CorrelationWeightSpectralBound
import D5.S3.Weil.ZetaLinear.PosIndex
import Mathlib.Algebra.Order.Round

/-! The eventual-existence reading of Stepanov--Herrmann--Guhr, Question III.5. -/

set_option autoImplicit false

open Matrix Finset
open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Estimation.CorrelationTopEigenvectorWeight

noncomputable section

/-- A real positive semidefinite matrix with unit diagonal. -/
def IsCorrelation {n : ℕ} (c : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  c.PosSemidef ∧ ∀ i, c i i = 1

/-- The mean over strictly lower triangular correlation coefficients. -/
def meanCorr {n : ℕ} (c : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  2 / ((n : ℝ) * ((n : ℝ) - 1)) * ∑ i, ∑ j with j < i, c i j

/-- The source standard deviation over the off-diagonal correlations. -/
def stdCorr {n : ℕ} (c : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (2 / ((n : ℝ) * ((n : ℝ) - 1)) *
    ∑ i, ∑ j with j < i, c i j ^ 2 - meanCorr c ^ 2)

/-- The normalized all-ones vector. -/
def delta (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (n : ℝ))⁻¹)

/-- Every top eigenvector has less weight than another vector in each eigenbasis. -/
def SatisfiesWGap {n : ℕ} (c : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (l : Fin n → ℝ),
    (∀ j, c *ᵥ (v j : Fin n → ℝ) = l j • (v j : Fin n → ℝ)) →
    ∀ i, (∀ j, l j ≤ l i) →
      ∃ j, j ≠ i ∧ ⟪v i, delta n⟫ ^ 2 < ⟪v j, delta n⟫ ^ 2

/-- The source domain A minus the union of A₁ and A₂. -/
def domainD (c σ : ℝ) : Prop :=
  (0 < c ∧ 0 < σ ∧ c ^ 2 + σ ^ 2 < 1) ∧
    ¬ (c ≥ 1 / 2 ∨ σ < c) ∧
    ¬ (σ > Real.sqrt 3 * c ∨ (c < σ ∧ σ < 1 - c))

/-- Question III.5 under the preregistered eventual-existence reading. -/
def claim : Prop :=
  ∀ c σ : ℝ, domainD c σ →
    ((∃ m : ℕ, ∀ n ≥ m, ∃ a : Matrix (Fin n) (Fin n) ℝ,
      IsCorrelation a ∧ meanCorr a = c ∧ stdCorr a = σ ∧ SatisfiesWGap a) ↔ c < σ)

private lemma domain_decomposition {c σ : ℝ} (h : domainD c σ) :
    0 < c ∧ c < 1 / 2 ∧ c ≤ σ ∧
      (σ = c ∨ (1 - c ≤ σ ∧ σ ≤ Real.sqrt 3 * c)) := by
  have hc : c < 1 / 2 := lt_of_not_ge fun hc => h.2.1 (Or.inl hc)
  have hcs : c ≤ σ := le_of_not_gt fun hcs => h.2.1 (Or.inr hcs)
  refine ⟨h.1.1, hc, hcs, ?_⟩
  by_cases heq : σ = c
  · exact Or.inl heq
  · right
    have hlt : c < σ := lt_of_le_of_ne hcs (Ne.symm heq)
    exact ⟨le_of_not_gt (fun hs => h.2.2 (Or.inr ⟨hlt, hs⟩)),
      le_of_not_gt (fun hs => h.2.2 (Or.inl hs))⟩

private lemma small_dimension_obstruction {n : ℕ} (hn : n ≤ 2)
    (a : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c) :
    ¬ (meanCorr a = c ∧ stdCorr a = c) := by
  intro h
  rcases n with _ | n
  · have hm : meanCorr a = 0 := by simp [meanCorr]
    linarith [h.1]
  rcases n with _ | n
  · have hm : meanCorr a = 0 := by simp [meanCorr]
    linarith [h.1]
  have hn0 : n = 0 := by omega
  subst n
  have hs : stdCorr a = 0 := by
    change stdCorr (n := 2) a = 0
    norm_num [stdCorr, meanCorr, sum_filter, Fin.sum_univ_two]
  linarith [h.2]

private lemma symmetric_sum {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = (∑ i, f i i) + 2 * ∑ i, ∑ j with j < i, f i j := by
  classical
  have hsplit : ∀ i j, f i j =
      (if j < i then f i j else 0) + (if i < j then f i j else 0) +
        (if i = j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, not_lt_of_ge hij.le]
    · subst j; simp
    · simp [hij, hij.ne.symm, not_lt_of_ge hij.le]
  have hupper : (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j with j < i, f i j := by
    rw [sum_comm]
    simp_rw [sum_filter]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hf j i]
  calc
    ∑ i, ∑ j, f i j = ∑ i, ∑ j,
        ((if j < i then f i j else 0) + (if i < j then f i j else 0) +
          (if i = j then f i j else 0)) :=
      sum_congr rfl fun i _ => sum_congr rfl fun j _ => hsplit i j
    _ = (∑ i, ∑ j with j < i, f i j) +
        (∑ i, ∑ j, if i < j then f i j else 0) + ∑ i, f i i := by
      simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_filter]
    _ = _ := by rw [hupper]; ring

private lemma delta_norm {n : ℕ} (hn : 0 < n) : ‖delta n‖ ^ 2 = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [← real_inner_self_eq_norm_sq]
  simp only [delta, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
    star_trivial, ← sq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [inv_pow, hs, mul_inv_cancel₀ hn0]

private lemma eigenbasis_rayleigh {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (l : Fin n → ℝ)
    (hv : ∀ j, a *ᵥ (v j : Fin n → ℝ) = l j • (v j : Fin n → ℝ))
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ j, l j * ⟪v j, u⟫ ^ 2 = ⟪u, a.toEuclideanLin u⟫ := by
  have hvlin : ∀ j, a.toEuclideanLin (v j) = l j • v j := by
    intro j
    exact (WithLp.equiv 2 _).injective (hv j)
  have hmap : a.toEuclideanLin u =
      ∑ j, ⟪v j, u⟫ • (l j • v j) := by
    calc
      a.toEuclideanLin u = a.toEuclideanLin (∑ j, ⟪v j, u⟫ • v j) :=
        congrArg a.toEuclideanLin (v.sum_repr' u).symm
      _ = _ := by rw [map_sum]; simp_rw [map_smul, hvlin]
  rw [hmap, inner_sum]
  exact sum_congr rfl fun j _ => by
    rw [inner_smul_right, inner_smul_right, real_inner_comm u (v j)]
    ring

private lemma correlation_rayleigh {n : ℕ} (hn : 3 ≤ n)
    (a : Matrix (Fin n) (Fin n) ℝ) (ha : IsCorrelation a) :
    ⟪delta n, a.toEuclideanLin (delta n)⟫ = 1 + ((n : ℝ) - 1) * meanCorr a := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hsym : ∀ i j, a i j = a j i := fun i j => ha.1.isHermitian.isSymm.apply j i
  have hsum := symmetric_sum (fun i j => a i j) hsym
  simp only [ha.2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hinner : ⟪delta n, a.toEuclideanLin (delta n)⟫ =
      (Real.sqrt (n : ℝ))⁻¹ ^ 2 * ∑ i, ∑ j, a i j := by
    change (a *ᵥ (fun _ => (Real.sqrt (n : ℝ))⁻¹)) ⬝ᵥ
      (star (fun _ => (Real.sqrt (n : ℝ))⁻¹)) = _
    simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, mul_sum, sum_mul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [hinner, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), hsum]
  dsimp only [meanCorr]
  field_simp
  <;> ring

private lemma correlation_centered_moments {n : ℕ} (hn : 3 ≤ n)
    (a : Matrix (Fin n) (Fin n) ℝ) (ha : IsCorrelation a) (hs : 0 < stdCorr a) :
    (∑ j, (ha.1.isHermitian.eigenvalues j - 1) = 0) ∧
      (∑ j, (ha.1.isHermitian.eigenvalues j - 1) ^ 2 =
        (n : ℝ) * ((n : ℝ) - 1) * (meanCorr a ^ 2 + stdCorr a ^ 2)) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have ht : ∑ j, ha.1.isHermitian.eigenvalues j = (n : ℝ) := by
    rw [← RHLinalg.rtrace_eq_sum_eigenvalues ha.1.isHermitian]
    simp [RHLinalg.rtrace, Matrix.trace, ha.2]
  have hf : ∑ j, ha.1.isHermitian.eigenvalues j ^ 2 =
      (n : ℝ) + 2 * ∑ i, ∑ j with j < i, a i j ^ 2 := by
    rw [← RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues ha.1.isHermitian]
    have hsym : ∀ i j, a i j ^ 2 = a j i ^ 2 := fun i j =>
      congrArg (fun t : ℝ => t ^ 2) (ha.1.isHermitian.isSymm.apply j i)
    have hsum := symmetric_sum (fun i j => a i j ^ 2) hsym
    simp only [ha.2, one_pow, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hsum
    convert hsum using 1
    simp only [RHLinalg.frobSq, Matrix.trace, diag_apply, mul_apply,
      conjTranspose_apply, star_trivial, RCLike.re_to_real, ← sq]
    exact sum_comm
  have hstd : stdCorr a ^ 2 = 2 / ((n : ℝ) * ((n : ℝ) - 1)) *
      ∑ i, ∑ j with j < i, a i j ^ 2 - meanCorr a ^ 2 := by
    exact Real.sq_sqrt ((Real.sqrt_pos.mp hs).le)
  constructor
  · simp only [sum_sub_distrib, ht, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sub_self]
  · have he : ∑ j, (ha.1.isHermitian.eigenvalues j - 1) ^ 2 =
        (∑ j, ha.1.isHermitian.eigenvalues j ^ 2) - 2 *
          (∑ j, ha.1.isHermitian.eigenvalues j) + n := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, one_pow, mul_one,
        ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [he, hf, ht, hstd]
    field_simp
    <;> ring

private lemma correlation_spectral_data {n : ℕ} (hn : 3 ≤ n)
    (a : Matrix (Fin n) (Fin n) ℝ) (ha : IsCorrelation a) (hs : 0 < stdCorr a)
    (hgap : SatisfiesWGap a) :
    ∃ (μ w : Fin n → ℝ) (i : Fin n),
      (∑ j, μ j = 0) ∧
      (∑ j, μ j ^ 2 = (n : ℝ) * ((n : ℝ) - 1) *
        (meanCorr a ^ 2 + stdCorr a ^ 2)) ∧
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∑ j, μ j * w j = ((n : ℝ) - 1) * meanCorr a) ∧
      (∀ j, μ j ≤ μ i) ∧ w i < 1 / 2 := by
  classical
  let v := ha.1.isHermitian.eigenvectorBasis
  let l := ha.1.isHermitian.eigenvalues
  have hne : (univ : Finset (Fin n)).Nonempty := by
    exact univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hi, htop⟩ := exists_max_image univ l hne
  have ht : ∀ j, l j ≤ l i := fun j => htop j (mem_univ j)
  have hv := ha.1.isHermitian.mulVec_eigenvectorBasis
  obtain ⟨j, hji, hweight⟩ := hgap v l hv i ht
  have hn0 : 0 < n := by omega
  have hws : ∑ j, ⟪v j, delta n⟫ ^ 2 = 1 := by
    rw [v.sum_sq_inner_right, delta_norm hn0]
  have hpair : ⟪v i, delta n⟫ ^ 2 + ⟪v j, delta n⟫ ^ 2 ≤ 1 := by
    have hle := sum_le_sum_of_subset_of_nonneg
      (show ({i, j} : Finset (Fin n)) ⊆ univ from subset_univ _)
      (fun k _ _ => sq_nonneg ⟪v k, delta n⟫)
    simpa [sum_pair hji.symm, hws] using hle
  obtain ⟨hm, he⟩ := correlation_centered_moments hn a ha hs
  refine ⟨fun j => l j - 1, fun j => ⟪v j, delta n⟫ ^ 2, i, hm, he,
    fun j => sq_nonneg _, hws, ?_, fun j => sub_le_sub_right (ht j) 1, by linarith⟩
  simp only [sub_mul, sum_sub_distrib, one_mul, hws]
  rw [eigenbasis_rayleigh a v l hv (delta n), correlation_rayleigh hn a ha]
  ring

private lemma segment_obstruction {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (hc : 0 < c) (ha : IsCorrelation a) (hm : meanCorr a = c)
    (hs : stdCorr a = c) : ¬ SatisfiesWGap a := by
  intro hgap
  by_cases hn : 3 ≤ n
  · obtain ⟨μ, w, i, hμ, he, hw, hws, hr, ht, hh⟩ :=
      correlation_spectral_data hn a ha (hs ▸ hc) hgap
    have hb := CorrelationWeightSpectralBound.centered_energy_strict
      hn (meanCorr a) (stdCorr a) (hm ▸ hc) μ w hμ he hw hws hr i ht hh
    rw [hm, hs] at hb
    exact (lt_irrefl _ hb)
  · exact small_dimension_obstruction (by omega) a c hc ⟨hm, hs⟩

private def wedgeX (c σ : ℝ) : ℝ :=
  ((σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) +
    min c ((σ ^ 2 - c ^ 2) / (c ^ 2 + σ ^ 2))) / 2

private lemma wedge_interval {c σ : ℝ} (h : domainD c σ) (hcs : c < σ) :
    0 ≤ (σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) ∧
      (σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) < wedgeX c σ ∧
      wedgeX c σ < min c ((σ ^ 2 - c ^ 2) / (c ^ 2 + σ ^ 2)) ∧
      min c ((σ ^ 2 - c ^ 2) / (c ^ 2 + σ ^ 2)) < 1 / 2 := by
  obtain ⟨hc, hc2, _, hd⟩ := domain_decomposition h
  have hσ : 0 < σ := h.1.2.1
  have hf : c ^ 2 + σ ^ 2 < 1 := h.1.2.2
  have hw : 1 - c ≤ σ := by
    rcases hd with hd | hd
    · linarith
    · exact hd.1
  have hc1 : 0 < 1 - c := by linarith
  have hden : 0 < σ ^ 2 + (1 - c) ^ 2 := by positivity
  have hf0 : 0 < c ^ 2 + σ ^ 2 := by positivity
  have hL : 0 ≤ (σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) := by
    apply div_nonneg _ hden.le
    nlinarith
  have hLc : (σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) < c := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hc1 (sub_pos.mpr hf)]
  have hLU : (σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) <
      (σ ^ 2 - c ^ 2) / (c ^ 2 + σ ^ 2) := by
    apply (div_lt_div_iff₀ hden hf0).mpr
    nlinarith [mul_pos (sq_pos_of_pos hσ) (show 0 < 1 - 2 * c by linarith)]
  have hmin := lt_min hLc hLU
  refine ⟨hL, ?_, ?_, lt_of_le_of_lt (min_le_left _ _) hc2⟩
  · dsimp only [wedgeX]; linarith
  · dsimp only [wedgeX]; linarith

private lemma wedge_parameters {c σ : ℝ} (h : domainD c σ) (hcs : c < σ) :
    let x := wedgeX c σ
    let a := σ / Real.sqrt (1 - x ^ 2)
    let b := c - a * x
    0 < x ∧ x < 1 / 2 ∧ x < c ∧
      0 < a ∧ 0 < b ∧ 0 < 1 - a - b ∧ 2 * c < a + b := by
  obtain ⟨hL, hLx, hxmin, hmhalf⟩ := wedge_interval h hcs
  let x := wedgeX c σ
  have hx0 : 0 < x := lt_of_le_of_lt hL hLx
  have hxhalf : x < 1 / 2 := hxmin.trans hmhalf
  have hxc : x < c := hxmin.trans_le (min_le_left _ _)
  have hxU : x < (σ ^ 2 - c ^ 2) / (c ^ 2 + σ ^ 2) :=
    hxmin.trans_le (min_le_right _ _)
  have hc : 0 < c := h.1.1
  have hσ : 0 < σ := h.1.2.1
  have hf : c ^ 2 + σ ^ 2 < 1 := h.1.2.2
  have hc2 : c < 1 / 2 := (domain_decomposition h).2.1
  have hq : 0 < Real.sqrt (1 - x ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hq2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hb : σ * x < c * Real.sqrt (1 - x ^ 2) := by
    have hx2 : x ^ 2 < c ^ 2 := (sq_lt_sq₀ hx0.le hc.le).mpr hxc
    have hxf := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hf.le)
    apply (sq_lt_sq₀ (mul_nonneg hσ.le hx0.le) (mul_nonneg hc.le hq.le)).mp
    rw [mul_pow, mul_pow, hq2]
    nlinarith only [hx2, hxf]
  have hd : σ * (1 - x) < (1 - c) * Real.sqrt (1 - x ^ 2) := by
    have hden : 0 < σ ^ 2 + (1 - c) ^ 2 := by positivity
    have hineq := (div_lt_iff₀ hden).mp hLx
    have hmul := mul_pos (show 0 < 1 - x by linarith)
      (show 0 < (1 - c) ^ 2 * (1 + x) - σ ^ 2 * (1 - x) by nlinarith only [hineq])
    apply (sq_lt_sq₀ (mul_nonneg hσ.le (by linarith))
      (mul_nonneg (by linarith) hq.le)).mp
    rw [mul_pow, mul_pow, hq2]
    nlinarith only [hmul]
  have hg : c * Real.sqrt (1 - x ^ 2) < σ * (1 - x) := by
    have hf0 : 0 < c ^ 2 + σ ^ 2 := by positivity
    have hineq := (lt_div_iff₀ hf0).mp hxU
    have hmul := mul_pos (show 0 < 1 - x by linarith)
      (show 0 < σ ^ 2 * (1 - x) - c ^ 2 * (1 + x) by nlinarith only [hineq])
    apply (sq_lt_sq₀ (mul_nonneg hc.le hq.le)
      (mul_nonneg hσ.le (by linarith))).mp
    rw [mul_pow, hq2, mul_pow]
    nlinarith only [hmul]
  dsimp only
  refine ⟨hx0, hxhalf, hxc, div_pos hσ hq, ?_, ?_, ?_⟩
  · apply sub_pos.mpr
    rw [div_mul_eq_mul_div, div_lt_iff₀ hq]
    exact hb
  · apply (mul_pos_iff_of_pos_right hq).mp
    change 0 < (1 - σ / Real.sqrt (1 - x ^ 2) -
      (c - σ / Real.sqrt (1 - x ^ 2) * x)) * Real.sqrt (1 - x ^ 2)
    convert sub_pos.mpr hd using 1 <;> field_simp <;> ring
  · apply (mul_lt_mul_iff_left₀ hq).mp
    change 2 * c * Real.sqrt (1 - x ^ 2) <
      (σ / Real.sqrt (1 - x ^ 2) + (c - σ / Real.sqrt (1 - x ^ 2) * x)) *
        Real.sqrt (1 - x ^ 2)
    have heq : (σ / Real.sqrt (1 - x ^ 2) + (c - σ / Real.sqrt (1 - x ^ 2) * x)) *
        Real.sqrt (1 - x ^ 2) = σ * (1 - x) + c * Real.sqrt (1 - x ^ 2) := by
      field_simp
      <;> ring
    rw [heq]
    linarith only [hg]

private def roundedCount (x : ℝ) (n : ℕ) : ℤ :=
  round ((n : ℝ) * (1 + Real.sqrt x) / 2)

private def signVector (n : ℕ) (k : ℤ) : Fin n → ℝ :=
  fun i => if (i.val : ℤ) < k then 1 else -1

private def roundedZ (n : ℕ) (k : ℤ) : ℝ :=
  ((2 * (k : ℝ) - (n : ℝ)) ^ 2 - (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1))

private def signMatrix (n : ℕ) (k : ℤ) (a b d : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  d • (1 : Matrix (Fin n) (Fin n) ℝ) +
    a • Matrix.vecMulVec (signVector n k) (signVector n k) +
    b • Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

private lemma rounded_eventually {c σ : ℝ} (h : domainD c σ) (hcs : c < σ)
    (hp : let x := wedgeX c σ
      let a := σ / Real.sqrt (1 - x ^ 2)
      let b := c - a * x
      0 < x ∧ x < 1 / 2 ∧ x < c ∧
        0 < a ∧ 0 < b ∧ 0 < 1 - a - b ∧ 2 * c < a + b) :
    ∃ m : ℕ, ∀ n ≥ m,
      let k := roundedCount (wedgeX c σ) n
      let z := roundedZ n k
      let a := σ / Real.sqrt (1 - z ^ 2)
      let b := c - a * z
      3 ≤ n ∧ 0 < k ∧ k < (n : ℤ) ∧ 2 * k ≠ (n : ℤ) ∧
        -1 < z ∧ z < 1 ∧ 0 < a ∧ 0 < b ∧ 0 < 1 - a - b ∧
        2 * ((n : ℝ) - 1) * c < ((n : ℝ) - 2) * (a + b) := by
  sorry

private lemma rank_two_realizes {n : ℕ} (hn : 3 ≤ n) (k : ℤ)
    (hk : 0 < k) (hkn : k < (n : ℤ)) (c σ : ℝ) (hσ : 0 < σ)
    (hz : -1 < roundedZ n k ∧ roundedZ n k < 1)
    (a b : ℝ) (ha : a = σ / Real.sqrt (1 - roundedZ n k ^ 2))
    (hb : b = c - a * roundedZ n k) (ha0 : 0 < a) (hb0 : 0 < b)
    (hd0 : 0 < 1 - a - b) :
    IsCorrelation (signMatrix n k a b (1 - a - b)) ∧
      meanCorr (signMatrix n k a b (1 - a - b)) = c ∧
      stdCorr (signMatrix n k a b (1 - a - b)) = σ := by
  sorry

private lemma rank_two_weight_gap {n : ℕ} (hn : 3 ≤ n) (k : ℤ)
    (hk : 0 < k) (hkn : k < (n : ℤ)) (hbalance : 2 * k ≠ (n : ℤ))
    (a b d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hgap : 2 * ((n : ℝ) - 1) * (a * roundedZ n k + b) <
      ((n : ℝ) - 2) * (a + b)) :
    SatisfiesWGap (signMatrix n k a b d) := by
  sorry

private lemma wedge_construction {c σ : ℝ} (h : domainD c σ) (hcs : c < σ) :
    ∃ m : ℕ, ∀ n ≥ m, ∃ a : Matrix (Fin n) (Fin n) ℝ,
      IsCorrelation a ∧ meanCorr a = c ∧ stdCorr a = σ ∧ SatisfiesWGap a := by
  obtain ⟨m, hm⟩ := rounded_eventually h hcs (wedge_parameters h hcs)
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨hn3, hk, hkn, hbal, hzl, hzu, ha, hb, hd, hineq⟩ := hm n hn
  let k := roundedCount (wedgeX c σ) n
  let a := σ / Real.sqrt (1 - roundedZ n k ^ 2)
  let b := c - a * roundedZ n k
  obtain ⟨hcorr, hmean, hstd⟩ := rank_two_realizes hn3 k hk hkn c σ h.1.2.1
    ⟨hzl, hzu⟩ a b rfl rfl ha hb hd
  refine ⟨signMatrix n k a b (1 - a - b), hcorr, hmean, hstd, ?_⟩
  apply rank_two_weight_gap hn3 k hk hkn hbal a b (1 - a - b) ha hb
  have heq : a * roundedZ n k + b = c := by dsimp [b]; ring
  rwa [heq]

/-- Eventual existence on the remaining domain is equivalent to σ being above c. -/
theorem result : claim := by
  intro c σ h
  constructor
  · intro hex
    have hd := domain_decomposition h
    by_contra hcs
    have heq : σ = c := le_antisymm (le_of_not_gt hcs) hd.2.2.1
    obtain ⟨m, hm⟩ := hex
    obtain ⟨a, ha, hmean, hstd, hgap⟩ := hm m le_rfl
    exact segment_obstruction a c hd.1 ha hmean (hstd.trans heq) hgap
  · exact wedge_construction h

end

end D5.S3.Estimation.CorrelationTopEigenvectorWeight
