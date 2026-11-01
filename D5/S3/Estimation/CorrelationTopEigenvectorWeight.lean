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

private lemma correlation_spectral_data {n : ℕ} (hn : 3 ≤ n)
    (a : Matrix (Fin n) (Fin n) ℝ) (ha : IsCorrelation a) (hgap : SatisfiesWGap a) :
    ∃ (μ w : Fin n → ℝ) (i : Fin n),
      (∑ j, μ j = 0) ∧
      (∑ j, μ j ^ 2 = (n : ℝ) * ((n : ℝ) - 1) *
        (meanCorr a ^ 2 + stdCorr a ^ 2)) ∧
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∑ j, μ j * w j = ((n : ℝ) - 1) * meanCorr a) ∧
      (∀ j, μ j ≤ μ i) ∧ w i < 1 / 2 := by
  sorry

private lemma segment_obstruction {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (hc : 0 < c) (ha : IsCorrelation a) (hm : meanCorr a = c)
    (hs : stdCorr a = c) : ¬ SatisfiesWGap a := by
  intro hgap
  by_cases hn : 3 ≤ n
  · obtain ⟨μ, w, i, hμ, he, hw, hws, hr, ht, hh⟩ :=
      correlation_spectral_data hn a ha hgap
    have hb := CorrelationWeightSpectralBound.centered_energy_strict
      hn (meanCorr a) (stdCorr a) (hm ▸ hc) μ w hμ he hw hws hr i ht hh
    rw [hm, hs] at hb
    exact (lt_irrefl _ hb)
  · exact small_dimension_obstruction (by omega) a c hc ⟨hm, hs⟩

private def wedgeX (c σ : ℝ) : ℝ :=
  ((σ ^ 2 - (1 - c) ^ 2) / (σ ^ 2 + (1 - c) ^ 2) +
    min c ((σ ^ 2 - c ^ 2) / (c ^ 2 + σ ^ 2))) / 2

private lemma wedge_parameters {c σ : ℝ} (h : domainD c σ) (hcs : c < σ) :
    let x := wedgeX c σ
    let a := σ / Real.sqrt (1 - x ^ 2)
    let b := c - a * x
    0 < x ∧ x < 1 / 2 ∧ x < c ∧
      0 < a ∧ 0 < b ∧ 0 < 1 - a - b ∧ 2 * c < a + b := by
  sorry

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
