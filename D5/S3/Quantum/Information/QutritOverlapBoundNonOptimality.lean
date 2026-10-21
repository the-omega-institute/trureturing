/- GID: D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/QutritOverlapBoundNonOptimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.claim; result=D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.result; claim=D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.claim
   digest: The overlap entropy bound is unattainable for qutrits at interior overlaps. -/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Tomography.MUB.MUBModeSymmetryBudget

/-! The Tsallis order-two overlap bound and its qutrit equality obstruction. -/

noncomputable section

open Matrix Complex
open D5.S3.Quantum.Tomography.MUB
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace D5.S3.Quantum.Information.QutritOverlapBoundNonOptimality

/-- Probabilities for measurement in the standard basis. -/
def probA (ρ : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 → ℝ := fun i => (ρ i i).re

/-- Probabilities for measurement after applying the unitary matrix. -/
def probB (T ρ : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 → ℝ :=
  fun j => ((T * ρ * Tᴴ) j j).re

/-- The source's function D, including its integer floor. -/
def boundD (θ : ℝ) : ℝ :=
  let m : ℝ := ⌊1 / Real.cos θ ^ 2⌋
  1 - (m * (Real.cos θ ^ 2) ^ 2 + (1 - m * Real.cos θ ^ 2) ^ 2)

/-- The overlap bound in equation (22). -/
def overlapBound (c : ℝ) : ℝ :=
  sInf ((fun θ => boundD θ + boundD (Real.arccos c - θ)) '' Set.Icc 0 (Real.arccos c))

/-- Attainment of the overlap bound by qutrit observables and a density matrix. -/
def claim : Prop :=
  ∀ c : ℝ, 1 / Real.sqrt 2 < c → c ≤ 1 →
    ∃ T ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      (∀ i j, ‖T i j‖ ≤ c) ∧ (∃ i j, ‖T i j‖ = c) ∧
      ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
        MUBModeSymmetryBudget.threeModeMixing (probA ρ) +
          MUBModeSymmetryBudget.threeModeMixing (probB T ρ) = overlapBound c

private lemma threshold_facts {c : ℝ} (hc : 1 / Real.sqrt 2 < c) :
    0 < c ∧ 1 / 2 < c ^ 2 ∧ Real.sqrt 2 / 2 < c := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have he : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hp)).mpr
    nlinarith
  rw [he] at hc
  exact ⟨by nlinarith [Real.sqrt_nonneg 2], by nlinarith, hc⟩

private lemma boundD_formula {c θ : ℝ} (hc : 1 / Real.sqrt 2 < c) (hc1 : c ≤ 1)
    (hθ : θ ∈ Set.Icc 0 (Real.arccos c)) :
    boundD θ = (1 - Real.cos (4 * θ)) / 4 := by
  obtain ⟨hc0, hc2, _⟩ := threshold_facts hc
  have hcos : c ≤ Real.cos θ := by
    rw [← Real.cos_arccos (by linarith : -1 ≤ c) hc1]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (Real.arccos_le_pi c) hθ.2
  have hcos0 : 0 < Real.cos θ := lt_of_lt_of_le hc0 hcos
  have hsq : 1 / 2 < Real.cos θ ^ 2 := by nlinarith
  have hsq1 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hm : ⌊1 / Real.cos θ ^ 2⌋ = (1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ (sq_pos_of_pos hcos0)).mpr
      simpa only [Int.cast_one, one_mul] using hsq1
    · apply (div_lt_iff₀ (sq_pos_of_pos hcos0)).mpr
      norm_num
      linarith
  unfold boundD
  rw [hm]
  norm_num only [Int.cast_one, one_mul]
  rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, Real.cos_two_mul]
  ring

private lemma overlapBound_eq {c : ℝ} (hc : 1 / Real.sqrt 2 < c) (hc1 : c ≤ 1) :
    overlapBound c = 1 - c ^ 2 := by
  obtain ⟨hc0, hc2, _⟩ := threshold_facts hc
  let γ := Real.arccos c
  have hγ : 0 ≤ γ := Real.arccos_nonneg c
  have hcos : Real.cos (2 * γ) = 2 * c ^ 2 - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith) hc1]
  have hpair (θ : ℝ) (hθ : θ ∈ Set.Icc 0 γ) :
      boundD θ + boundD (γ - θ) =
        (1 - (2 * c ^ 2 - 1) * Real.cos (4 * θ - 2 * γ)) / 2 := by
    rw [boundD_formula hc hc1 hθ, boundD_formula hc hc1 ⟨by linarith [hθ.2],
      by linarith [hθ.1]⟩]
    have h := Real.cos_add_cos (4 * θ) (4 * (γ - θ))
    rw [show (4 * θ + 4 * (γ - θ)) / 2 = 2 * γ by ring,
      show (4 * θ - 4 * (γ - θ)) / 2 = 4 * θ - 2 * γ by ring, hcos] at h
    nlinarith only [h]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨γ / 2, ⟨by linarith, by linarith⟩, ?_⟩
    change boundD (γ / 2) + boundD (γ - γ / 2) = 1 - c ^ 2
    rw [hpair (γ / 2) ⟨by linarith, by linarith⟩]
    rw [show 4 * (γ / 2) - 2 * γ = 0 by ring, Real.cos_zero]
    ring
  · rintro _ ⟨θ, hθ, rfl⟩
    change 1 - c ^ 2 ≤ boundD θ + boundD (γ - θ)
    rw [hpair θ hθ]
    nlinarith [Real.cos_le_one (4 * θ - 2 * γ)]

private lemma entropy_small (p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hm : ∀ i, p i ≤ 1 / 2) : 1 / 2 ≤ MUBModeSymmetryBudget.threeModeMixing p := by
  have h : ∑ i, p i ^ 2 ≤ ∑ i, p i / 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hp i, hm i]
  rw [← Finset.sum_div, hs] at h
  rw [Fin.sum_univ_three] at h
  unfold MUBModeSymmetryBudget.threeModeMixing MUBModeSymmetryBudget.threeModeCollision
  linarith

private lemma entropy_maximum (p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (i : Fin 3) :
    2 * p i * (1 - p i) ≤ MUBModeSymmetryBudget.threeModeMixing p ∧
      (MUBModeSymmetryBudget.threeModeMixing p = 2 * p i * (1 - p i) → ∃ k, k ≠ i ∧ p k = 0) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  rw [Fin.sum_univ_three] at hs
  unfold MUBModeSymmetryBudget.threeModeMixing MUBModeSymmetryBudget.threeModeCollision
  fin_cases i <;> dsimp only
  · change 2 * p 0 * (1 - p 0) ≤ 1 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) ∧ _
    have hp0 : p 0 = 1 - p 1 - p 2 := by linarith
    constructor
    · rw [hp0]
      nlinarith [mul_nonneg h1 h2]
    · intro he
      change 1 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) = 2 * p 0 * (1 - p 0) at he
      rw [hp0] at he
      have hz : p 1 * p 2 = 0 := by nlinarith only [he]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact ⟨1, by decide, hz⟩
      · exact ⟨2, by decide, hz⟩
  · change 2 * p 1 * (1 - p 1) ≤ 1 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) ∧ _
    have hp1 : p 1 = 1 - p 0 - p 2 := by linarith
    constructor
    · rw [hp1]
      nlinarith [mul_nonneg h0 h2]
    · intro he
      change 1 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) = 2 * p 1 * (1 - p 1) at he
      rw [hp1] at he
      have hz : p 0 * p 2 = 0 := by nlinarith only [he]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact ⟨0, by decide, hz⟩
      · exact ⟨2, by decide, hz⟩
  · change 2 * p 2 * (1 - p 2) ≤ 1 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) ∧ _
    have hp2 : p 2 = 1 - p 0 - p 1 := by linarith
    constructor
    · rw [hp2]
      nlinarith [mul_nonneg h0 h1]
    · intro he
      change 1 - (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) = 2 * p 2 * (1 - p 2) at he
      rw [hp2] at he
      have hz : p 0 * p 1 = 0 := by nlinarith only [he]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact ⟨0, by decide, hz⟩
      · exact ⟨1, by decide, hz⟩

private lemma ellipse_bound {P Q t c : ℝ} (hP : 1 / 2 < P) (hQ : 1 / 2 < Q)
    (ht0 : 0 ≤ t) (htc : t ≤ c) (hc2 : 1 / 2 < c ^ 2)
    (hc1 : c < 1)
    (he : (2 * P - 1) ^ 2 + (2 * Q - 1) ^ 2 -
      2 * (2 * t ^ 2 - 1) * (2 * P - 1) * (2 * Q - 1) ≤
      1 - (2 * t ^ 2 - 1) ^ 2) :
    1 - c ^ 2 ≤ 2 * P * (1 - P) + 2 * Q * (1 - Q) ∧
      (2 * P * (1 - P) + 2 * Q * (1 - Q) = 1 - c ^ 2 →
        P = (1 + c) / 2 ∧ Q = (1 + c) / 2) := by
  have ht1 : t < 1 := lt_of_le_of_lt htc hc1
  have ht2 : t ^ 2 ≤ c ^ 2 := by nlinarith
  by_cases hz : 2 * t ^ 2 - 1 ≤ 0
  · have hxy := mul_pos (show 0 < 2 * P - 1 by linarith)
      (show 0 < 2 * Q - 1 by linarith)
    have hprod := mul_nonpos_of_nonpos_of_nonneg hz hxy.le
    have hs : (2 * P - 1) ^ 2 + (2 * Q - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (2 * t ^ 2 - 1)]
    constructor
    · nlinarith
    · intro heq
      exfalso
      nlinarith
  · have hz0 : 0 < 2 * t ^ 2 - 1 := lt_of_not_ge hz
    have hz1 : 0 < 1 - (2 * t ^ 2 - 1) := by nlinarith
    have hdiff := mul_nonneg hz0.le (sq_nonneg ((2 * P - 1) - (2 * Q - 1)))
    have hs : (2 * P - 1) ^ 2 + (2 * Q - 1) ^ 2 ≤ 2 * t ^ 2 := by
      by_contra hn
      have hm := mul_pos hz1 (show 0 <
        (2 * P - 1) ^ 2 + (2 * Q - 1) ^ 2 - 2 * t ^ 2 by linarith)
      nlinarith
    constructor
    · nlinarith
    · intro heq
      have hteq : t ^ 2 = c ^ 2 := by nlinarith
      have hPQ : P = Q := by
        have hzero : ((2 * P - 1) - (2 * Q - 1)) ^ 2 = 0 := by
          nlinarith
        nlinarith [sq_nonneg (P - Q)]
      constructor <;> nlinarith

private lemma overlap_ellipse (x a b : EuclideanSpace ℂ (Fin 3))
    (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hP : 1 / 2 < ‖⟪x, a⟫_ℂ‖ ^ 2) (hQ : 1 / 2 < ‖⟪x, b⟫_ℂ‖ ^ 2) :
    (2 * ‖⟪x, a⟫_ℂ‖ ^ 2 - 1) ^ 2 + (2 * ‖⟪x, b⟫_ℂ‖ ^ 2 - 1) ^ 2 -
      2 * (2 * ‖⟪a, b⟫_ℂ‖ ^ 2 - 1) *
        (2 * ‖⟪x, a⟫_ℂ‖ ^ 2 - 1) * (2 * ‖⟪x, b⟫_ℂ‖ ^ 2 - 1) ≤
      1 - (2 * ‖⟪a, b⟫_ℂ‖ ^ 2 - 1) ^ 2 := by
  let α := ⟪x, a⟫_ℂ
  let β := ⟪x, b⟫_ℂ
  let τ := ⟪a, b⟫_ℂ
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hi : ⟪a - α • x, b - β • x⟫_ℂ = τ - conj α * β := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hxx, ← inner_conj_symm a x]
    change τ - conj α * β - β * (conj α - conj α * 1) = τ - conj α * β
    ring
  have hresidual (v : EuclideanSpace ℂ (Fin 3)) (hv : ‖v‖ = 1) :
      ‖v - ⟪x, v⟫_ℂ • x‖ ^ 2 = 1 - ‖⟪x, v⟫_ℂ‖ ^ 2 := by
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection v (ℂ ∙ x)
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton] at h
    rw [hx, hv, one_pow] at h
    change 1 = ‖(⟪x, v⟫_ℂ / (1 : ℂ)) • x‖ ^ 2 +
      ‖v - (⟪x, v⟫_ℂ / (1 : ℂ)) • x‖ ^ 2 at h
    rw [div_one, norm_smul, hx, mul_one] at h
    linarith
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (a - α • x) (b - β • x)
  have hcs2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
  rw [hi, mul_pow, hresidual a ha, hresidual b hb] at hcs2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq] at hcs2
  have hn := Complex.re_le_norm (τ * conj (conj α * β))
  rw [norm_mul, norm_conj, norm_mul, norm_conj] at hn
  have hg : 0 ≤ ‖α‖ ^ 2 + ‖β‖ ^ 2 + ‖τ‖ ^ 2 - 1 := by
    nlinarith [sq_nonneg ‖τ‖]
  have hle : ‖α‖ ^ 2 + ‖β‖ ^ 2 + ‖τ‖ ^ 2 - 1 ≤
      2 * (‖τ‖ * (‖α‖ * ‖β‖)) := by nlinarith
  have hsq := (sq_le_sq₀ hg (by positivity : 0 ≤ 2 * (‖τ‖ * (‖α‖ * ‖β‖)))).mpr hle
  change (2 * ‖α‖ ^ 2 - 1) ^ 2 + (2 * ‖β‖ ^ 2 - 1) ^ 2 -
    2 * (2 * ‖τ‖ ^ 2 - 1) * (2 * ‖α‖ ^ 2 - 1) * (2 * ‖β‖ ^ 2 - 1) ≤
    1 - (2 * ‖τ‖ ^ 2 - 1) ^ 2
  nlinarith only [hsq]

private lemma saturation_vector (x a b : EuclideanSpace ℂ (Fin 3))
    (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {c : ℝ} (hc : 0 < c)
    (hab : ‖⟪a, b⟫_ℂ‖ ≤ c)
    (hP : ‖⟪a, x⟫_ℂ‖ ^ 2 = (1 + c) / 2)
    (hQ : ‖⟪b, x⟫_ℂ‖ ^ 2 = (1 + c) / 2) :
    ((1 + c : ℝ) : ℂ) • x = ⟪a, x⟫_ℂ • a + ⟪b, x⟫_ℂ • b := by
  let u := ⟪a, x⟫_ℂ
  let v := ⟪b, x⟫_ℂ
  have hnorm : ‖u‖ = ‖v‖ := by nlinarith [norm_nonneg u, norm_nonneg v]
  have hn := Complex.re_le_norm (conj u * (v * ⟪a, b⟫_ℂ))
  rw [norm_mul, norm_conj, norm_mul] at hn
  have hcross : (conj u * (v * ⟪a, b⟫_ℂ)).re ≤ c * ((1 + c) / 2) := by
    have hm := mul_le_mul_of_nonneg_left hab (mul_nonneg (norm_nonneg u) (norm_nonneg v))
    rw [← hnorm] at hn hm
    nlinarith
  have hinner : ⟪x, u • a + v • b⟫_ℂ = ((1 + c : ℝ) : ℂ) := by
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      ← inner_conj_symm x a, ← inner_conj_symm x b]
    change u * conj u + v * conj v = _
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hP, hQ]
    push_cast
    ring
  have hzero : ‖((1 + c : ℝ) : ℂ) • x - (u • a + v • b)‖ ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    rw [norm_sub_sq (𝕜 := ℂ), norm_smul, hx, mul_one, inner_smul_left, hinner,
      norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, ha, hb, mul_one, mul_one,
      inner_smul_left, inner_smul_right]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.conj_ofReal,
      ← Complex.ofReal_mul]
    change (1 + c) ^ 2 - 2 * ((1 + c) * (1 + c)) +
      (‖u‖ ^ 2 + 2 * (conj u * (v * ⟪a, b⟫_ℂ)).re + ‖v‖ ^ 2) ≤ 0
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

private lemma qutrit_sum {R : Type*} [AddCommMonoid R] (f : Fin 3 → R)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ r, f r = f i + f j + f k := by
  have hs : ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hij, hik, hjk]
  rw [← hs]
  simp [hij, hik, hjk, add_assoc]

private lemma zero_corner (T : Matrix (Fin 3) (Fin 3) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hTc : ∀ i j, ‖T i j‖ < 1)
    {i j k l : Fin 3} (hjl : j ≠ l) (hik : i ≠ k)
    (hjk : T j k = 0) (hli : T l i = 0) : False := by
  classical
  have hcard : ({j, l} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by
    simp [hjl]
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  let U : Matrix.unitaryGroup (Fin 3) ℂ := ⟨T, hT⟩
  have hi := Matrix.unitaryGroup_row_norm U i
  have hk := Matrix.unitaryGroup_row_norm U k
  change ∑ s, ‖T s i‖ ^ 2 = 1 at hi
  change ∑ s, ‖T s k‖ ^ 2 = 1 at hk
  rw [qutrit_sum _ hjl (Ne.symm hr.1) (Ne.symm hr.2), hli, norm_zero, zero_pow (by decide),
    add_zero] at hi
  have hri : T r i ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by decide), add_zero] at hi
    nlinarith [hTc j i, norm_nonneg (T j i)]
  have hor := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i k) hT.1
  change ∑ s, conj (T s i) * T s k = (1 : Matrix (Fin 3) (Fin 3) ℂ) i k at hor
  rw [Matrix.one_apply_ne hik, qutrit_sum _ hjl (Ne.symm hr.1) (Ne.symm hr.2),
    hjk, hli, map_zero, mul_zero, zero_mul, zero_add] at hor
  simp only [zero_add] at hor
  have hric : conj (T r i) ≠ 0 := by
    intro hz
    apply hri
    have he := congrArg conj hz
    simpa only [map_zero, starRingEnd_self_apply] using he
  have hrk : T r k = 0 := (mul_eq_zero.mp hor).resolve_left hric
  rw [qutrit_sum _ hjl (Ne.symm hr.1) (Ne.symm hr.2), hjk, hrk, norm_zero,
    zero_pow (by decide), zero_add, add_zero] at hk
  nlinarith [hTc l k, norm_nonneg (T l k)]

private lemma pure_strict {c : ℝ} (hc : 1 / Real.sqrt 2 < c) (hc1 : c < 1)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hTc : ∀ i j, ‖T i j‖ ≤ c) (ψ : Fin 3 → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    1 - c ^ 2 < MUBModeSymmetryBudget.threeModeMixing (fun i => ‖ψ i‖ ^ 2) +
      MUBModeSymmetryBudget.threeModeMixing (fun j => ‖(T *ᵥ ψ) j‖ ^ 2) := by
  let x : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ψ
  let y : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 (T *ᵥ ψ)
  let p : Fin 3 → ℝ := fun i => ‖ψ i‖ ^ 2
  let q : Fin 3 → ℝ := fun j => ‖(T *ᵥ ψ) j‖ ^ 2
  have hx : ‖x‖ = 1 := by
    have hs : ‖x‖ ^ 2 = 1 := by rw [EuclideanSpace.norm_sq_eq]; exact hψ
    nlinarith [norm_nonneg x]
  have hy : ‖y‖ = 1 := by
    have hu : Tᴴ * T = 1 := hT.1
    have hi : ⟪y, y⟫_ℂ = ⟪x, x⟫_ℂ := by
      rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.inner_A_mulVec_eq, hu,
        Matrix.one_mulVec, EuclideanSpace.inner_eq_star_dotProduct]
      exact dotProduct_comm _ _
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hs : ‖y‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast hi
    nlinarith [norm_nonneg y]
  have hq : ∑ j, q j = 1 := by
    rw [← EuclideanSpace.norm_sq_eq y, hy]
    norm_num
  have hp0 (i : Fin 3) : 0 ≤ p i := sq_nonneg _
  have hq0 (j : Fin 3) : 0 ≤ q j := sq_nonneg _
  obtain ⟨hc0, hc2, _⟩ := threshold_facts hc
  by_cases hpSmall : ∀ i, p i ≤ 1 / 2
  · have hsmall := entropy_small p hp0 hψ hpSmall
    have hnonneg : 0 ≤ MUBModeSymmetryBudget.threeModeMixing q :=
      MUBModeSymmetryBudget.threeModeMixing_nonneg q hq0
        (by simpa only [Fin.sum_univ_three] using hq)
    change 1 - c ^ 2 < MUBModeSymmetryBudget.threeModeMixing p + MUBModeSymmetryBudget.threeModeMixing q
    linarith
  by_cases hqSmall : ∀ j, q j ≤ 1 / 2
  · have hsmall := entropy_small q hq0 hq hqSmall
    have hnonneg : 0 ≤ MUBModeSymmetryBudget.threeModeMixing p :=
      MUBModeSymmetryBudget.threeModeMixing_nonneg p hp0
        (by simpa only [Fin.sum_univ_three] using hψ)
    change 1 - c ^ 2 < MUBModeSymmetryBudget.threeModeMixing p + MUBModeSymmetryBudget.threeModeMixing q
    linarith
  push Not at hpSmall hqSmall
  obtain ⟨i, hP⟩ := hpSmall
  obtain ⟨j, hQ⟩ := hqSmall
  let a := EuclideanSpace.basisFun (Fin 3) ℂ i
  let b : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 (fun k => conj (T j k))
  have ha : ‖a‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal.1 i
  have hb : ‖b‖ = 1 := by
    let U : Matrix.unitaryGroup (Fin 3) ℂ := ⟨T, hT⟩
    have hs : ‖b‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Matrix.unitaryGroup_row_norm (star U) j
    nlinarith [norm_nonneg b]
  have hax : ⟪a, x⟫_ℂ = ψ i := EuclideanSpace.basisFun_inner (𝕜 := ℂ) (ι := Fin 3) x i
  have hbx : ⟪b, x⟫_ℂ = (T *ᵥ ψ) j := by
    simp [b, x, EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.mulVec, mul_comm]
  have hab : ‖⟪a, b⟫_ℂ‖ = ‖T j i‖ := by
    rw [EuclideanSpace.basisFun_inner (𝕜 := ℂ) (ι := Fin 3) b i]
    exact norm_conj _
  have hxp : ‖⟪x, a⟫_ℂ‖ ^ 2 = p i := by rw [norm_inner_symm, hax]
  have hxq : ‖⟪x, b⟫_ℂ‖ ^ 2 = q j := by rw [norm_inner_symm, hbx]
  have he := overlap_ellipse x a b hx ha hb (hxp ▸ hP) (hxq ▸ hQ)
  rw [hxp, hxq, hab] at he
  obtain ⟨hbound, hequal⟩ := ellipse_bound hP hQ (norm_nonneg _) (hTc j i) hc2 hc1 he
  obtain ⟨hpBound, hpZero⟩ := entropy_maximum p hp0 hψ i
  obtain ⟨hqBound, hqZero⟩ := entropy_maximum q hq0 hq j
  change 1 - c ^ 2 < MUBModeSymmetryBudget.threeModeMixing p + MUBModeSymmetryBudget.threeModeMixing q
  by_contra hn
  have heq : 2 * p i * (1 - p i) + 2 * q j * (1 - q j) = 1 - c ^ 2 := by
    linarith
  obtain ⟨hPi, hQj⟩ := hequal heq
  obtain ⟨k, hki, hpk⟩ := hpZero (by linarith)
  obtain ⟨l, hlj, hql⟩ := hqZero (by linarith)
  have hψk : ψ k = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hpk)
  have hψl : (T *ᵥ ψ) l = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hql)
  have hψi : ψ i ≠ 0 := by
    intro hz
    simp only [p, hz, norm_zero] at hP
    norm_num at hP
  have hψj : (T *ᵥ ψ) j ≠ 0 := by
    intro hz
    simp only [q, hz, norm_zero] at hQ
    norm_num at hQ
  have hv := saturation_vector x a b hx ha hb hc0 (hab ▸ hTc j i)
    (by rw [hax]; exact hPi) (by rw [hbx]; exact hQj)
  rw [hax, hbx] at hv
  have hjk : T j k = 0 := by
    have hk := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => z k) hv
    have hz : (T *ᵥ ψ) j * conj (T j k) = 0 := by
      simpa [x, a, b, EuclideanSpace.basisFun_apply, hki, hki.symm, hψk] using hk.symm
    have := (mul_eq_zero.mp hz).resolve_left hψj
    simpa only [map_eq_zero] using this
  have hraw : ((1 + c : ℝ) : ℂ) • ψ =
      ψ i • Pi.single i 1 + (T *ᵥ ψ) j • (fun k => conj (T j k)) := by
    have ht := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z) hv
    simpa only [WithLp.ofLp_smul, WithLp.ofLp_add, a, EuclideanSpace.basisFun_apply,
      PiLp.ofLp_single] using ht
  have hrow : T *ᵥ (fun k => conj (T j k)) = Pi.single j 1 := by
    ext r
    have hr := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M r j) hT.2
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply,
      eq_comm] using hr
  have ht := congrArg (Matrix.mulVec T) hraw
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_single_one, hrow] at ht
  have hli : T l i = 0 := by
    have hl := congrFun ht l
    have hz : ψ i * T l i = 0 := by
      simpa [Pi.smul_apply, Pi.add_apply, Pi.single_apply, hlj, hlj.symm, hψl] using hl.symm
    exact (mul_eq_zero.mp hz).resolve_left hψi
  exact zero_corner T hT (fun r s => lt_of_le_of_lt (hTc r s) hc1)
    hlj.symm hki.symm hjk hli

private lemma entropy_mixture (w : Fin 3 → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : ∑ k, w k = 1) (p : Fin 3 → Fin 3 → ℝ) :
    ∑ k, w k * MUBModeSymmetryBudget.threeModeMixing (p k) ≤ MUBModeSymmetryBudget.threeModeMixing (fun i => ∑ k, w k * p k i) := by
  have hj (i : Fin 3) : (∑ k, w k * p k i) ^ 2 ≤ ∑ k, w k * p k i ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun k => w k * p k i) (f := w) (g := fun k => w k * p k i ^ 2)
      (fun k _ => hw k) (fun k _ => mul_nonneg (hw k) (sq_nonneg _))
      (fun k _ => le_of_eq (by ring))
    rwa [hs, one_mul] at h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj i)
  have he : (∑ k, w k * MUBModeSymmetryBudget.threeModeMixing (p k)) = 1 - ∑ i, ∑ k, w k * p k i ^ 2 := by
    simp only [MUBModeSymmetryBudget.threeModeMixing, mul_sub, mul_one,
      Finset.sum_sub_distrib, hs]
    congr 1
    unfold MUBModeSymmetryBudget.threeModeCollision
    simp only [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    conv_rhs => rw [Fin.sum_univ_three]
  rw [he]
  unfold MUBModeSymmetryBudget.threeModeMixing MUBModeSymmetryBudget.threeModeCollision
  rw [Fin.sum_univ_three]
  change 1 - ((∑ k, w k * p k 0 ^ 2) +
      (∑ k, w k * p k 1 ^ 2) + (∑ k, w k * p k 2 ^ 2)) ≤
    1 - ((∑ k, w k * p k 0) ^ 2 +
      (∑ k, w k * p k 1) ^ 2 + (∑ k, w k * p k 2) ^ 2)
  simp only [Fin.sum_univ_three]
  simp only [Fin.sum_univ_three] at hsum
  linarith

private lemma strict_overlap_bound {c : ℝ} (hc : 1 / Real.sqrt 2 < c) (hc1 : c < 1)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hTc : ∀ i j, ‖T i j‖ ≤ c) (ρ : Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    overlapBound c < MUBModeSymmetryBudget.threeModeMixing (probA ρ) + MUBModeSymmetryBudget.threeModeMixing (probB T ρ) := by
  rw [overlapBound_eq hc hc1.le]
  let U := hρ.1.eigenvectorUnitary
  let wgt := hρ.1.eigenvalues
  let V : Matrix.unitaryGroup (Fin 3) ℂ := (⟨T, hT⟩ : Matrix.unitaryGroup (Fin 3) ℂ) * U
  have hwgt (k : Fin 3) : 0 ≤ wgt k := hρ.eigenvalues_nonneg k
  have hsum : ∑ k, wgt k = 1 := by
    have ht := hρ.1.trace_eq_sum_eigenvalues
    rw [htrace] at ht
    have hs : ((∑ k, wgt k : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      exact ht.symm
    exact Complex.ofReal_injective hs
  have hdec : ρ = (U : Matrix (Fin 3) (Fin 3) ℂ) *
      Matrix.diagonal (fun k => (wgt k : ℂ)) * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ :=
    hρ.1.spectral_theorem
  have hdecB : T * ρ * Tᴴ = (V : Matrix (Fin 3) (Fin 3) ℂ) *
      Matrix.diagonal (fun k => (wgt k : ℂ)) * (V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ := by
    calc
      T * ρ * Tᴴ = T * ((U : Matrix (Fin 3) (Fin 3) ℂ) *
          Matrix.diagonal (fun k => (wgt k : ℂ)) * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) * Tᴴ :=
        congrArg (fun A => T * A * Tᴴ) hdec
      _ = _ := by
        change _ = (T * (U : Matrix (Fin 3) (Fin 3) ℂ)) *
          Matrix.diagonal (fun k => (wgt k : ℂ)) * (T * (U : Matrix (Fin 3) (Fin 3) ℂ))ᴴ
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  have hdiagonal (W : Matrix.unitaryGroup (Fin 3) ℂ) (i : Fin 3) :
      (((W : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.diagonal (fun k => (wgt k : ℂ)) *
        (W : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) i i).re = ∑ k, wgt k * ‖W i k‖ ^ 2 := by
    have h := D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projected_dynamics_is_unistochastic
      (W : Matrix (Fin 3) (Fin 3) ℂ) wgt W.prop
    have hr := congrFun (h.2.2.2 0) i
    simpa only [D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectedWeights,
      D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectedOrbit,
      D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectedStep,
      D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.projectiveReadout,
      D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.unitaryEvolution,
      D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState,
      Matrix.diagonal_apply_eq, Matrix.diag_apply, Matrix.mulVec, dotProduct,
      Complex.ofReal_re, Matrix.star_eq_conjTranspose, h.2.1, mul_comm] using hr
  have hpA : probA ρ = fun i => ∑ k, wgt k * ‖U i k‖ ^ 2 := by
    funext i
    exact (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => (A i i).re) hdec).trans
      (hdiagonal U i)
  have hpB : probB T ρ = fun j => ∑ k, wgt k * ‖V j k‖ ^ 2 := by
    funext j
    exact (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => (A j j).re) hdecB).trans
      (hdiagonal V j)
  have hp := entropy_mixture wgt hwgt hsum (fun k i => ‖U i k‖ ^ 2)
  have hq := entropy_mixture wgt hwgt hsum (fun k j => ‖V j k‖ ^ 2)
  have hall (k : Fin 3) : 1 - c ^ 2 <
      MUBModeSymmetryBudget.threeModeMixing (fun i => ‖U i k‖ ^ 2) + MUBModeSymmetryBudget.threeModeMixing (fun j => ‖V j k‖ ^ 2) := by
    have h := pure_strict hc hc1 T hT hTc (fun i => U i k)
      (Matrix.unitaryGroup_row_norm U k)
    exact h
  obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => hwgt k)).mp
    (show 0 < ∑ k, wgt k by rw [hsum]; norm_num)
  have hstrict : (∑ k, wgt k * (1 - c ^ 2)) <
      ∑ k, wgt k * (MUBModeSymmetryBudget.threeModeMixing (fun i => ‖U i k‖ ^ 2) +
        MUBModeSymmetryBudget.threeModeMixing (fun j => ‖V j k‖ ^ 2)) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact mul_le_mul_of_nonneg_left (hall k).le (hwgt k)
    · exact ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left (hall k) hk⟩
  rw [← Finset.sum_mul, hsum, one_mul] at hstrict
  simp only [mul_add, Finset.sum_add_distrib] at hstrict
  rw [hpA, hpB]
  linarith

theorem result : ¬ claim := by
  intro h
  have hc : 1 / Real.sqrt 2 < (3 / 4 : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  obtain ⟨T, hT, hTc, _, ρ, hρ, htrace, he⟩ := h (3 / 4) hc (by norm_num)
  exact (strict_overlap_bound hc (by norm_num) T hT hTc ρ hρ htrace).ne' he

end D5.S3.Quantum.Information.QutritOverlapBoundNonOptimality
