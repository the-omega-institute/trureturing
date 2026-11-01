/- GID: D5/S3/Estimation/CorrelationTopEigenvectorWeight
   generality: G
   mirror-B: D5/B/S3/Estimation/CorrelationTopEigenvectorWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The remaining correlation domain admits the weight gap exactly above sigma=c. -/

import D5.S3.Weil.ZetaLinear.PosIndex

/-! The eventual-existence reading of Stepanov--Herrmann--Guhr, Question III.5. -/

set_option autoImplicit false

open Matrix Finset Filter
open scoped BigOperators RealInnerProductSpace ComplexOrder Topology

namespace D5.S3.Estimation.CorrelationTopEigenvectorWeight

noncomputable section

private lemma two_point_energy {n : ℕ} (hn : 3 ≤ n) (μ : Fin n → ℝ)
    (hsum : ∑ j, μ j = 0) (i j : Fin n) (hij : i ≠ j) :
    (n : ℝ) * (μ i + μ j) ^ 2 ≤
      2 * ((n : ℝ) - 2) * ∑ k, μ k ^ 2 := by
  classical
  let s := (univ.erase i).erase j
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨hij.symm, mem_univ _⟩
  have hcard : (s.card : ℝ) = (n : ℝ) - 2 := by
    simp only [s, card_erase_of_mem hj, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
    ring
  have hrest : ∑ k ∈ s, μ k = -(μ i + μ j) := by
    dsimp only [s]
    rw [sum_erase_eq_sub hj, sum_erase_eq_sub (mem_univ i), hsum]
    ring
  have hrestsq : (∑ k ∈ s, μ k ^ 2) + (μ i ^ 2 + μ j ^ 2) =
      ∑ k, μ k ^ 2 := by
    dsimp only [s]
    rw [sum_erase_eq_sub hj, sum_erase_eq_sub (mem_univ i)]
    ring
  have hcs := sum_mul_sq_le_sq_mul_sq s μ (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one, hrest, hcard,
    neg_sq] at hcs
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) - 2 := by linarith
  have hpair := mul_nonneg hn0 (sq_nonneg (μ i - μ j))
  nlinarith [hrestsq]

private lemma top_pair_of_weights {n : ℕ} (hn : 3 ≤ n) (μ w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (i : Fin n)
    (htop : ∀ j, μ j ≤ μ i) (hhalf : w i < 1 / 2) :
    ∃ j, j ≠ i ∧ 2 * (∑ k, μ k * w k) ≤ μ i + μ j := by
  classical
  have hne : (univ.erase i).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, hmax⟩ := exists_max_image (univ.erase i) μ hne
  refine ⟨j, (mem_erase.mp hj).1, ?_⟩
  have hsumle : ∑ k ∈ univ.erase i, μ k * w k ≤
      μ j * ∑ k ∈ univ.erase i, w k := by
    rw [mul_sum]
    exact sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hmax k hk) (hw k)
  have hrest : ∑ x ∈ univ.erase i, w x = 1 - w i := by
    rw [sum_erase_eq_sub (mem_univ i), hsum]
  rw [hrest] at hsumle
  have hsm := sum_erase_add univ (fun k => μ k * w k) (mem_univ i)
  have hdiff := mul_nonneg (sub_nonneg.mpr (htop j))
    (show 0 ≤ 1 / 2 - w i by linarith)
  nlinarith

/-- A top spectral weight below one half forces a larger centered second moment. -/
private theorem centered_energy_strict {n : ℕ} (hn : 3 ≤ n) (c σ : ℝ) (hc : 0 < c)
    (μ w : Fin n → ℝ) (hμ : ∑ j, μ j = 0)
    (henergy : ∑ j, μ j ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (c ^ 2 + σ ^ 2))
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (hrayleigh : ∑ j, μ j * w j = ((n : ℝ) - 1) * c)
    (i : Fin n) (htop : ∀ j, μ j ≤ μ i) (hhalf : w i < 1 / 2) :
    c ^ 2 < σ ^ 2 := by
  obtain ⟨j, hji, hpair⟩ := top_pair_of_weights hn μ w hw hsum i htop hhalf
  have hbound := two_point_energy hn μ hμ i j hji.symm
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) - 2 := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  rw [hrayleigh] at hpair
  have hpair0 : 0 < μ i + μ j := lt_of_lt_of_le (by positivity) hpair
  have hsquare : (2 * ((n : ℝ) - 1) * c) ^ 2 ≤ (μ i + μ j) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  rw [henergy] at hbound
  have hlarge : 2 * (n : ℝ) * ((n : ℝ) - 1) ^ 2 * c ^ 2 ≤
      ((n : ℝ) - 2) * (n : ℝ) * ((n : ℝ) - 1) * (c ^ 2 + σ ^ 2) := by
    nlinarith only [hbound,
      mul_le_mul_of_nonneg_left hsquare (show 0 ≤ (n : ℝ) by positivity)]
  have hcancel : 2 * ((n : ℝ) - 1) * c ^ 2 ≤
      ((n : ℝ) - 2) * (c ^ 2 + σ ^ 2) := by
    have hnpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by positivity
    apply (mul_le_mul_iff_right₀ hnpos).mp
    nlinarith only [hlarge]
  by_contra h
  have hle : σ ^ 2 ≤ c ^ 2 := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_left hle hn2.le
  nlinarith [sq_pos_of_pos hc]

/-- A two-column factorization and a strict half-trace estimate force a larger weight
away from any maximal diagonal entry. -/
private theorem weight_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ e s : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hdiag : ∀ i j, (if i = j then μ i else 0) =
      a * (s i * s j) + b * (e i * e j))
    (hgap : 2 * (∑ j, μ j * e j ^ 2) < (∑ j, μ j) * ∑ j, e j ^ 2)
    (i : ι) (htop : ∀ j, μ j ≤ μ i) :
    ∃ j, j ≠ i ∧ e i ^ 2 < e j ^ 2 := by
  classical
  have hself : ∀ j, μ j = a * s j ^ 2 + b * e j ^ 2 := by
    intro j
    simpa only [ite_true, ← sq] using hdiag j j
  have hμ : ∀ j, 0 ≤ μ j := fun j => by rw [hself]; positivity
  have hzero : ∀ j, μ j = 0 → e j = 0 := by
    intro j hj
    have hz : b * e j ^ 2 = 0 :=
      ((add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (sq_nonneg (s j)))
        (mul_nonneg hb.le (sq_nonneg (e j)))).mp ((hself j).symm.trans hj)).2
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hb.ne')
  let x : Matrix ι (Fin 2) ℝ := fun j t => if t = 0 then a * s j else b * e j
  let y : Matrix (Fin 2) ι ℝ := fun t j => if t = 0 then s j else e j
  have hfactor : diagonal μ = x * y := by
    ext j k
    change (if j = k then μ j else 0) = ∑ t : Fin 2, x j t * y t k
    simp only [Fin.sum_univ_two]
    norm_num [x, y, mul_assoc]
    exact hdiag j k
  let t := univ.filter (fun j => μ j ≠ 0)
  have hcard : t.card ≤ 2 := by
    have hr : (diagonal μ).rank ≤ 2 := by
      rw [hfactor]
      exact (rank_mul_le_left x y).trans (by simpa using rank_le_card_width x)
    simpa only [rank_diagonal, Fintype.card_subtype, t] using hr
  have hex : ∃ j, j ≠ i ∧ μ j ≠ 0 := by
    by_contra h
    have hz : ∀ j, j ≠ i → μ j = 0 := by
      intro j hji
      by_contra hj
      exact h ⟨j, hji, hj⟩
    have hm : ∑ j, μ j = μ i := by
      apply sum_eq_single i
      · intro j _ hji; exact hz j hji
      · simp
    have he : ∑ j, e j ^ 2 = e i ^ 2 := by
      apply sum_eq_single i
      · intro j _ hji; rw [hzero j (hz j hji)]; norm_num
      · simp
    have hme : ∑ j, μ j * e j ^ 2 = μ i * e i ^ 2 := by
      apply sum_eq_single i
      · intro j _ hji; rw [hz j hji, zero_mul]
      · simp
    rw [hm, he, hme] at hgap
    nlinarith only [hgap, mul_nonneg (hμ i) (sq_nonneg (e i))]
  obtain ⟨j, hji, hjμ⟩ := hex
  have hiμ : μ i ≠ 0 := ne_of_gt ((lt_of_le_of_ne (hμ j) hjμ.symm).trans_le (htop j))
  have hi : i ∈ t := mem_filter.mpr ⟨mem_univ _, hiμ⟩
  have hj : j ∈ t.erase i := mem_erase.mpr ⟨hji, mem_filter.mpr ⟨mem_univ _, hjμ⟩⟩
  have hrest : (t.erase i).card ≤ 1 := by rw [card_erase_of_mem hi]; omega
  have hz : ∀ k, k ≠ i → k ≠ j → μ k = 0 := by
    intro k hki hkj
    by_contra hk
    have hkt : k ∈ t.erase i := mem_erase.mpr ⟨hki, mem_filter.mpr ⟨mem_univ _, hk⟩⟩
    exact hkj (card_le_one.mp hrest k hkt j hj)
  have hsum : ∀ f : ι → ℝ, (∀ k, k ≠ i → k ≠ j → f k = 0) →
      ∑ k, f k = f i + f j := by
    intro f hf
    exact sum_eq_add i j hji.symm (fun k _ hk => hf k hk.1 hk.2)
      (by simp) (by simp)
  have hm := hsum μ hz
  have he := hsum (fun k => e k ^ 2) (fun k hki hkj => by rw [hzero k (hz k hki hkj)]; norm_num)
  have hme := hsum (fun k => μ k * e k ^ 2)
    (fun k hki hkj => by rw [hz k hki hkj, zero_mul])
  rw [hm, he, hme] at hgap
  refine ⟨j, hji, ?_⟩
  by_contra h
  have hd := mul_nonneg (sub_nonneg.mpr (htop j)) (sub_nonneg.mpr (le_of_not_gt h))
  nlinarith only [hgap, hd]

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
  have h := sum_sum_Ioi_add_eq_sum_sum_off_diag (α := (Fin n)ᵒᵈ) f
  simp only [← filter_lt_eq_Ioi] at h
  change (∑ i, ∑ j with j < i, (f j i + f i j)) = _ at h
  have hs : ∀ i j, f j i + f i j = 2 * f i j := by
    intro i j
    rw [hf j i]
    ring
  simp_rw [hs] at h
  simp only [← mul_sum, compl_singleton,
    sum_erase_eq_sub (mem_univ _), sum_sub_distrib] at h
  rw [sum_comm] at h
  change 2 * (∑ i : Fin n, ∑ j with j < i, f i j) =
    (∑ i : Fin n, ∑ j, f i j) - ∑ i : Fin n, f i i at h
  linarith only [h]

private lemma delta_norm {n : ℕ} (hn : 0 < n) : ‖delta n‖ ^ 2 = 1 := by
  rw [delta.eq_1, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.toLp_apply, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    mul_inv_cancel₀ (by exact_mod_cast hn.ne')]

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
    rw [dotProduct_comm, dot_mulVec_eq_sum_sum]
    simp only [Pi.star_apply, star_trivial, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [hinner, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), hsum]
  dsimp only [meanCorr]
  field_simp (disch := first | assumption | positivity | linarith)

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
    dsimp only [RHLinalg.rtrace]
    simp [Matrix.trace, ha.2]
  have hf : ∑ j, ha.1.isHermitian.eigenvalues j ^ 2 =
      (n : ℝ) + 2 * ∑ i, ∑ j with j < i, a i j ^ 2 := by
    rw [← RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues ha.1.isHermitian]
    have hsym : ∀ i j, a i j ^ 2 = a j i ^ 2 := fun i j =>
      congrArg (fun t : ℝ => t ^ 2) (ha.1.isHermitian.isSymm.apply j i)
    have hsum := symmetric_sum (fun i j => a i j ^ 2) hsym
    simp only [ha.2, one_pow, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hsum
    convert hsum using 1
    dsimp only [RHLinalg.frobSq]
    simp only [Matrix.trace, diag_apply, mul_apply,
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
    field_simp (disch := first | assumption | positivity | linarith)
    ring

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
    exact univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by omega))
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
    have hb := centered_energy_strict
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
    convert sub_pos.mpr hd using 1
    field_simp (disch := first | assumption | positivity | linarith)
    ring
  · apply (mul_lt_mul_iff_left₀ hq).mp
    change 2 * c * Real.sqrt (1 - x ^ 2) <
      (σ / Real.sqrt (1 - x ^ 2) + (c - σ / Real.sqrt (1 - x ^ 2) * x)) *
        Real.sqrt (1 - x ^ 2)
    have heq : (σ / Real.sqrt (1 - x ^ 2) + (c - σ / Real.sqrt (1 - x ^ 2) * x)) *
        Real.sqrt (1 - x ^ 2) = σ * (1 - x) + c * Real.sqrt (1 - x ^ 2) := by
      field_simp (disch := first | assumption | positivity | linarith)
      ring
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

private lemma signVector_sq (n : ℕ) (k : ℤ) (i : Fin n) :
    signVector n k i ^ 2 = 1 := by
  dsimp only [signVector]
  split_ifs <;> norm_num

private lemma signVector_sum {n : ℕ} (k : ℤ) (hk : 0 < k) (hkn : k < (n : ℤ)) :
    ∑ i, signVector n k i = 2 * (k : ℝ) - (n : ℝ) := by
  classical
  let t : Fin n := ⟨k.toNat, by omega⟩
  have htest : ∀ i : Fin n, ((i.val : ℤ) < k) ↔ i < t := by
    intro i
    change (i.val : ℤ) < k ↔ i.val < k.toNat
    omega
  have hsign : ∀ i : Fin n, signVector n k i = 2 * (if i < t then 1 else 0) - 1 := by
    intro i
    dsimp only [signVector]
    simp only [htest]
    split_ifs <;> norm_num
  have hcount : (∑ i : Fin n, if i < t then (1 : ℝ) else 0) = (k.toNat : ℝ) := by
    rw [← sum_filter]
    simp only [filter_gt_eq_Iio, sum_const, nsmul_eq_mul, mul_one, Fin.card_Iio, t]
  have hkcast : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk.le
  simp_rw [hsign]
  rw [sum_sub_distrib, ← mul_sum, hcount, hkcast]
  simp

private lemma lower_sign_moments {n : ℕ} (k : ℤ) (hk : 0 < k)
    (hkn : k < (n : ℤ)) :
    (2 * ∑ i : Fin n, ∑ j with j < i, (1 : ℝ) = (n : ℝ) * ((n : ℝ) - 1)) ∧
      (2 * ∑ i, ∑ j with j < i, signVector n k i * signVector n k j =
        (2 * (k : ℝ) - (n : ℝ)) ^ 2 - (n : ℝ)) := by
  classical
  have hone : 2 * ∑ i : Fin n, ∑ j with j < i, (1 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    have h := Finset.card_product_filter_lt (s := (univ : Finset (Fin n)))
    have hc : (∑ i : Fin n, ∑ j with j < i, (1 : ℝ)) = (n.choose 2 : ℝ) := by
      calc
        _ = ∑ p : Fin n × Fin n, if p.1 < p.2 then (1 : ℝ) else 0 := by
          simp only [Fintype.sum_prod_type, sum_filter]
          rw [sum_comm]
        _ = ((univ.product univ).filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
          rw [sum_boole]
          simp
        _ = (n.choose 2 : ℝ) := by
          simpa only [product_eq_sprod, card_univ, Fintype.card_fin] using
            congrArg (fun a : ℕ => (a : ℝ)) h
    rw [hc, Nat.cast_choose_two]
    ring
  have hs := symmetric_sum (fun i j => signVector n k i * signVector n k j)
    (fun i j => mul_comm _ _)
  have hdiag : (∑ i, signVector n k i * signVector n k i) = (n : ℝ) := by
    simp only [← sq, signVector_sq, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have htotal : (∑ i, ∑ j, signVector n k i * signVector n k j) =
      (2 * (k : ℝ) - (n : ℝ)) ^ 2 := by
    simp only [← mul_sum, ← sum_mul, signVector_sum k hk hkn, sq]
  rw [hdiag, htotal] at hs
  constructor
  · exact hone
  · nlinarith only [hs]

private lemma rounded_ratio_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => (roundedCount x n : ℝ) / (n : ℝ)) atTop
      (𝓝 ((1 + Real.sqrt x) / 2)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' (a := fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ)⁻¹)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hr := abs_sub_round ((n : ℝ) * (1 + Real.sqrt x) / 2)
    have hbound := mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr hnpos.le)
    rw [Real.norm_eq_abs]
    calc
      |(roundedCount x n : ℝ) / (n : ℝ) - (1 + Real.sqrt x) / 2| =
          |((roundedCount x n : ℝ) - (n : ℝ) * (1 + Real.sqrt x) / 2) / (n : ℝ)| := by
        congr 1
        field_simp (disch := first | assumption | positivity | linarith)
      _ = |(n : ℝ) * (1 + Real.sqrt x) / 2 - (roundedCount x n : ℝ)| *
          (n : ℝ)⁻¹ := by
        rw [abs_div, abs_of_pos hnpos, abs_sub_comm, div_eq_mul_inv]
      _ ≤ _ := hbound
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)

private lemma roundedZ_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => roundedZ n (roundedCount x n)) atTop (𝓝 x) := by
  have hr := rounded_ratio_tendsto x
  have hi := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ht := ((((hr.const_mul 2).sub_const 1).pow 2).sub hi).div
    (hi.const_sub 1) (show (1 : ℝ) - 0 ≠ 0 by norm_num)
  have heq : (2 * ((1 + Real.sqrt x) / 2) - 1) ^ 2 = x := by
    convert Real.sq_sqrt hx using 1
    ring
  simp only [sub_zero, div_one, heq] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  change ((2 * ((roundedCount x n : ℝ) / (n : ℝ)) - 1) ^ 2 - (n : ℝ)⁻¹) /
    (1 - (n : ℝ)⁻¹) = roundedZ n (roundedCount x n)
  dsimp only [roundedZ]
  field_simp (disch := first | assumption | positivity | linarith)

private lemma rounded_eventually {c σ : ℝ}
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
  dsimp only at hp
  obtain ⟨hx0, hxhalf, _, ha0, hb0, hd0, hgap0⟩ := hp
  let x := wedgeX c σ
  let an := fun n : ℕ => σ / Real.sqrt (1 - roundedZ n (roundedCount x n) ^ 2)
  let bn := fun n : ℕ => c - an n * roundedZ n (roundedCount x n)
  have hq : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr (by nlinarith only [hx0, hxhalf])
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs1 : Real.sqrt x < 1 := by nlinarith only [hsq, Real.sqrt_nonneg x, hxhalf]
  have hr := rounded_ratio_tendsto x
  have hz := roundedZ_tendsto x hx0.le
  have hi := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have han : Tendsto an atTop (𝓝 (σ / Real.sqrt (1 - x ^ 2))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub (hz.pow 2)).sqrt hq.ne'
  have hbn : Tendsto bn atTop (𝓝 (c - σ / Real.sqrt (1 - x ^ 2) * x)) :=
    tendsto_const_nhds.sub (han.mul hz)
  have hdn := (han.const_sub 1).sub hbn
  have hgn := ((((hi.const_mul 2).const_sub 1).mul (han.add hbn)).sub
    (((hi.const_sub 1).const_mul 2).mul_const c))
  simp only [mul_zero, sub_zero, one_mul, mul_one] at hgn
  have hev : ∀ᶠ n : ℕ in atTop,
      3 ≤ n ∧ 1 / 2 < (roundedCount x n : ℝ) / (n : ℝ) ∧
        (roundedCount x n : ℝ) / (n : ℝ) < 1 ∧
        -1 < roundedZ n (roundedCount x n) ∧ roundedZ n (roundedCount x n) < 1 ∧
        0 < an n ∧ 0 < bn n ∧ 0 < 1 - an n - bn n ∧
        0 < (1 - 2 * (n : ℝ)⁻¹) * (an n + bn n) -
          2 * (1 - (n : ℝ)⁻¹) * c := by
    filter_upwards [eventually_ge_atTop 3,
      hr.eventually_const_lt (show 1 / 2 < (1 + Real.sqrt x) / 2 by linarith),
      hr.eventually_lt_const (show (1 + Real.sqrt x) / 2 < 1 by linarith),
      hz.eventually_const_lt (show -1 < x by linarith),
      hz.eventually_lt_const (show x < 1 by linarith),
      han.eventually_const_lt ha0, hbn.eventually_const_lt hb0,
      hdn.eventually_const_lt hd0, hgn.eventually_const_lt (sub_pos.mpr hgap0)]
      with n hn hr0 hr1 hz0 hz1 ha hb hd hg
    exact ⟨hn, hr0, hr1, hz0, hz1, ha, hb, hd, hg⟩
  obtain ⟨m, hm⟩ := eventually_atTop.mp hev
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨hn3, hr0, hr1, hz0, hz1, ha, hb, hd, hg⟩ := hm n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hk0 := (lt_div_iff₀ hnpos).mp hr0
  have hk1 := (div_lt_iff₀ hnpos).mp hr1
  refine ⟨hn3, ?_, ?_, ?_, hz0, hz1, ha, hb, hd, ?_⟩
  · have hk : 0 < (roundedCount x n : ℝ) := by linarith
    exact_mod_cast hk
  · have hk : (roundedCount x n : ℝ) < (n : ℝ) := by simpa using hk1
    exact_mod_cast hk
  · intro heq
    have heqreal : 2 * (roundedCount x n : ℝ) = (n : ℝ) := by exact_mod_cast heq
    linarith
  · have hmul := mul_pos hg hnpos
    have heq : ((1 - 2 * (n : ℝ)⁻¹) * (an n + bn n) -
        2 * (1 - (n : ℝ)⁻¹) * c) * (n : ℝ) =
        ((n : ℝ) - 2) * (an n + bn n) - 2 * ((n : ℝ) - 1) * c := by
      field_simp (disch := first | assumption | positivity | linarith)
    rw [heq] at hmul
    exact sub_pos.mp hmul

private lemma rank_two_realizes {n : ℕ} (hn : 3 ≤ n) (k : ℤ)
    (hk : 0 < k) (hkn : k < (n : ℤ)) (c σ : ℝ) (hσ : 0 < σ)
    (hz : -1 < roundedZ n k ∧ roundedZ n k < 1)
    (a b : ℝ) (ha : a = σ / Real.sqrt (1 - roundedZ n k ^ 2))
    (hb : b = c - a * roundedZ n k) (ha0 : 0 < a) (hb0 : 0 < b)
    (hd0 : 0 < 1 - a - b) :
    IsCorrelation (signMatrix n k a b (1 - a - b)) ∧
      meanCorr (signMatrix n k a b (1 - a - b)) = c ∧
      stdCorr (signMatrix n k a b (1 - a - b)) = σ := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hq : 0 < Real.sqrt (1 - roundedZ n k ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [hz.1, hz.2])
  have hq2 : Real.sqrt (1 - roundedZ n k ^ 2) ^ 2 = 1 - roundedZ n k ^ 2 :=
    Real.sq_sqrt (by nlinarith [hz.1, hz.2])
  have hcorr : IsCorrelation (signMatrix n k a b (1 - a - b)) := by
    constructor
    · have hs : (vecMulVec (signVector n k) (signVector n k)).PosSemidef := by
        simpa only [star_trivial] using posSemidef_vecMulVec_self_star (signVector n k)
      have he : (vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ => 1)).PosSemidef := by
        simpa only [star_trivial] using
          posSemidef_vecMulVec_self_star (fun _ : Fin n => (1 : ℝ))
      exact ((PosSemidef.one.smul hd0.le).add (hs.smul ha0.le)).add (he.smul hb0.le)
    · intro i
      dsimp only [signMatrix]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply_eq,
        vecMulVec_apply, mul_one, ← sq, signVector_sq]
      ring
  obtain ⟨hcount, hsign⟩ := lower_sign_moments k hk hkn
  have hcountEq : (∑ i : Fin n, ∑ j with j < i, (1 : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by linarith only [hcount]
  have hsignEq : (∑ i, ∑ j with j < i, signVector n k i * signVector n k j) =
      ((2 * (k : ℝ) - (n : ℝ)) ^ 2 - (n : ℝ)) / 2 := by linarith only [hsign]
  have hentry : ∀ i j : Fin n, j < i →
      signMatrix n k a b (1 - a - b) i j = a * (signVector n k i * signVector n k j) + b := by
    intro i j hij
    dsimp only [signMatrix]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply,
      ite_eq_right hij.ne.symm, vecMulVec_apply, mul_one, mul_zero, zero_add]
  have hmean : meanCorr (signMatrix n k a b (1 - a - b)) = c := by
    have hsum : (∑ i, ∑ j with j < i, signMatrix n k a b (1 - a - b) i j) =
        a * (∑ i, ∑ j with j < i, signVector n k i * signVector n k j) +
          b * (∑ i : Fin n, ∑ j with j < i, (1 : ℝ)) := by
      calc
        _ = ∑ i, ∑ j with j < i, (a * (signVector n k i * signVector n k j) + b) :=
          sum_congr rfl fun i _ => sum_congr rfl fun j hj => hentry i j (mem_filter.mp hj).2
        _ = _ := by simp only [mul_sum, mul_one, ← sum_add_distrib]
    rw [meanCorr, hsum, hcountEq, hsignEq, hb]
    dsimp only [roundedZ]
    field_simp (disch := first | assumption | positivity | linarith)
    ring
  refine ⟨hcorr, hmean, ?_⟩
  have hsecond : (∑ i, ∑ j with j < i,
      signMatrix n k a b (1 - a - b) i j ^ 2) =
      (a ^ 2 + b ^ 2) * (∑ i : Fin n, ∑ j with j < i, (1 : ℝ)) +
        2 * a * b * (∑ i, ∑ j with j < i, signVector n k i * signVector n k j) := by
    calc
      _ = ∑ i, ∑ j with j < i, ((a ^ 2 + b ^ 2) +
          2 * a * b * (signVector n k i * signVector n k j)) := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j hj
        rw [hentry i j (mem_filter.mp hj).2]
        have hs : (signVector n k i * signVector n k j) ^ 2 = 1 := by
          rw [mul_pow, signVector_sq, signVector_sq, one_mul]
        calc
          _ = a ^ 2 * (signVector n k i * signVector n k j) ^ 2 + b ^ 2 +
              2 * a * b * (signVector n k i * signVector n k j) := by ring
          _ = _ := by rw [hs, mul_one]
      _ = _ := by simp only [mul_sum, mul_one, ← sum_add_distrib]
  have hvar : 2 / ((n : ℝ) * ((n : ℝ) - 1)) *
      (∑ i, ∑ j with j < i, signMatrix n k a b (1 - a - b) i j ^ 2) - c ^ 2 = σ ^ 2 := by
    have hamean : c = a * roundedZ n k + b := by rw [hb]; ring
    have hasq : a ^ 2 * (1 - roundedZ n k ^ 2) = σ ^ 2 := by
      rw [ha, div_pow, hq2]
      exact div_mul_cancel₀ _ (by nlinarith [hz.1, hz.2])
    have hsecondEq : 2 / ((n : ℝ) * ((n : ℝ) - 1)) *
        (∑ i, ∑ j with j < i, signMatrix n k a b (1 - a - b) i j ^ 2) =
        a ^ 2 + b ^ 2 + 2 * a * b * roundedZ n k := by
      rw [hsecond, hcountEq, hsignEq]
      dsimp only [roundedZ]
      field_simp (disch := first | assumption | positivity | linarith)
    rw [hsecondEq, hamean]
    nlinarith only [hasq]
  rw [stdCorr, hmean, hvar, Real.sqrt_sq hσ.le]

private lemma signMatrix_action {n : ℕ} (k : ℤ) (a b d : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    (signMatrix n k a b d).toEuclideanLin y =
      d • y + (a * ⟪WithLp.toLp 2 (signVector n k), y⟫) •
        WithLp.toLp 2 (signVector n k) +
      (b * ⟪WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)), y⟫) •
        WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)) := by
  apply WithLp.ofLp_injective 2
  dsimp only [signMatrix]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    WithLp.ofLp_add, WithLp.ofLp_smul, add_mulVec, smul_mulVec, one_mulVec,
    vecMulVec_mulVec, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  rw [dotProduct_comm (signVector n k),
    dotProduct_comm (fun _ : Fin n => (1 : ℝ))]
  ring

private lemma rank_two_weight_gap {n : ℕ} (hn : 3 ≤ n) (k : ℤ)
    (hk : 0 < k) (hkn : k < (n : ℤ))
    (a b d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hgap : 2 * ((n : ℝ) - 1) * (a * roundedZ n k + b) <
      ((n : ℝ) - 2) * (a + b)) :
    SatisfiesWGap (signMatrix n k a b d) := by
  intro v l hv i htop
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  let s : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (signVector n k)
  let e := fun j => ⟪v j, u⟫
  let f := fun j => ⟪v j, s⟫
  let μ := fun j => l j - d
  have hnormu : ‖u‖ ^ 2 = (n : ℝ) := by
    simpa only [u, PiLp.toLp_apply, one_pow, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using EuclideanSpace.real_norm_sq_eq u
  have hnorms : ‖s‖ ^ 2 = (n : ℝ) := by
    simpa only [s, PiLp.toLp_apply, signVector_sq, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using EuclideanSpace.real_norm_sq_eq s
  have heu : ∑ j, e j ^ 2 = (n : ℝ) := by rw [v.sum_sq_inner_right, hnormu]
  have hfs : ∑ j, f j ^ 2 = (n : ℝ) := by rw [v.sum_sq_inner_right, hnorms]
  have hvs : ∀ j, (signMatrix n k a b d).toEuclideanLin (v j) = l j • v j :=
    fun j => (WithLp.equiv 2 _).injective (hv j)
  have hdiag : ∀ j t, (if j = t then μ j else 0) =
      a * (f j * f t) + b * (e j * e t) := by
    intro j t
    have heq := congrArg (fun y => ⟪v j, y⟫) (hvs t)
    rw [signMatrix_action] at heq
    simp only [inner_add_right, inner_smul_right] at heq
    change d * ⟪v j, v t⟫ + a * ⟪s, v t⟫ * ⟪v j, s⟫ +
      b * ⟪u, v t⟫ * ⟪v j, u⟫ = l t * ⟪v j, v t⟫ at heq
    rw [real_inner_comm (v t) s, real_inner_comm (v t) u] at heq
    have hort := orthonormal_iff_ite.mp v.orthonormal j t
    rw [hort] at heq
    by_cases hjt : j = t
    · subst t
      simp only [ite_true, mul_one] at heq ⊢
      dsimp only [μ, f, e]
      nlinarith only [heq]
    · simp only [hjt, ite_false, mul_zero] at heq ⊢
      dsimp only [f, e]
      nlinarith only [heq]
  have htrace : ∑ j, μ j = (n : ℝ) * (a + b) := by
    have hself : ∀ j, μ j = a * f j ^ 2 + b * e j ^ 2 := by
      intro j
      simpa only [ite_true, ← sq] using hdiag j j
    simp_rw [hself]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hfs, heu]
    ring
  have hdot : ⟪u, s⟫ = 2 * (k : ℝ) - (n : ℝ) := by
    simpa only [u, s, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
      star_trivial, mul_one] using signVector_sum k hk hkn
  have henergy : ∑ j, μ j * e j ^ 2 =
      a * (2 * (k : ℝ) - (n : ℝ)) ^ 2 + b * (n : ℝ) ^ 2 := by
    dsimp only [μ, e]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
    rw [eigenbasis_rayleigh (signMatrix n k a b d) v l hv u,
      signMatrix_action, inner_add_right, inner_add_right,
      inner_smul_right, inner_smul_right, inner_smul_right]
    change d * ⟪u, u⟫ + a * ⟪s, u⟫ * ⟪u, s⟫ + b * ⟪u, u⟫ * ⟪u, u⟫ -
      d * (∑ j, e j ^ 2) = _
    rw [real_inner_comm u s, hdot, real_inner_self_eq_norm_sq, hnormu]
    rw [heu]
    ring
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hscalar : 2 * (∑ j, μ j * e j ^ 2) < (∑ j, μ j) * ∑ j, e j ^ 2 := by
    rw [henergy, htrace, heu]
    have hmul := mul_lt_mul_of_pos_right hgap hnpos
    dsimp only [roundedZ] at hmul
    field_simp (disch := first | assumption | positivity | linarith) at hmul
    nlinarith only [hmul]
  obtain ⟨j, hji, hweight⟩ := weight_gap μ e f a b ha hb hdiag
    hscalar i (fun j => sub_le_sub_right (htop j) d)
  refine ⟨j, hji, ?_⟩
  have hd : delta n = (Real.sqrt (n : ℝ))⁻¹ • u := by
    apply WithLp.ofLp_injective 2
    ext t
    dsimp only [delta, u]
    simp
  rw [hd, inner_smul_right, inner_smul_right, mul_pow, mul_pow]
  exact mul_lt_mul_of_pos_left hweight (by positivity)

private lemma wedge_construction {c σ : ℝ} (h : domainD c σ) (hcs : c < σ) :
    ∃ m : ℕ, ∀ n ≥ m, ∃ a : Matrix (Fin n) (Fin n) ℝ,
      IsCorrelation a ∧ meanCorr a = c ∧ stdCorr a = σ ∧ SatisfiesWGap a := by
  obtain ⟨m, hm⟩ := rounded_eventually (wedge_parameters h hcs)
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨hn3, hk, hkn, _hbal, hzl, hzu, ha, hb, hd, hineq⟩ := hm n hn
  let k := roundedCount (wedgeX c σ) n
  let a := σ / Real.sqrt (1 - roundedZ n k ^ 2)
  let b := c - a * roundedZ n k
  obtain ⟨hcorr, hmean, hstd⟩ := rank_two_realizes hn3 k hk hkn c σ h.1.2.1
    ⟨hzl, hzu⟩ a b rfl rfl ha hb hd
  refine ⟨signMatrix n k a b (1 - a - b), hcorr, hmean, hstd, ?_⟩
  apply rank_two_weight_gap hn3 k hk hkn a b (1 - a - b) ha hb
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
