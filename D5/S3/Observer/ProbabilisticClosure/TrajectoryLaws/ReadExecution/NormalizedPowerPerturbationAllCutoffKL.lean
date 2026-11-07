/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/NormalizedPowerPerturbationAllCutoffKL
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/NormalizedPowerPerturbationAllCutoffKL
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: WIP: normalized countable power perturbations and every finite collapsed cutoff. -/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

/-!
WIP source for the E3 atom of
`FIB_ENTROPY_HARMONIC_RENEWAL_STATE_THRESHOLD`.

The target deliberately keeps the infinite normalizers and the complete
`Option (Fin L)` carrier.  `none` is the whole tail `k > L`; a short index
`r : Fin L` denotes the physical count `r.val + 1`.  The theorem is left open
until the two-reference full-series energy estimate and the finite-to-countable
tail Cauchy passage have a kernel proof.  This file is not frozen or deposited.
-/

open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource

set_option autoImplicit false

open Filter Finset
open scoped Topology

private lemma power_increment (m k : ℕ) (hm : 1 ≤ m) :
    ((k + 1 : ℕ) : ℝ) ^ (m - 1) ≤
      ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
  have he : m = (m - 1) + 1 := by omega
  have hp : (k : ℝ) ^ (m - 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (m - 1) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ k) _
  have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) k)
  rw [he, pow_succ, pow_succ]
  push_cast
  nlinarith

private lemma adjacent_power_sum (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 0 < s) :
    powerSum (m - 1) s ≤ (1 - Real.exp (-s)) * powerSum m s := by
  have ha := summable_term m hs
  have hb := summable_term (m - 1) hs
  have hc : Summable (fun k : ℕ => term m s (k + 1)) :=
    (summable_nat_add_iff 1).2 ha
  have hsum : (∑' k : ℕ, term m s (k + 1)) = powerSum m s := by
    simpa [powerSum, term] using ha.tsum_eq_zero_add
  have hshift : ∀ k : ℕ,
      Real.exp (-s) * term m s k =
        (k : ℝ) ^ m * Real.exp (-s * ((k + 1 : ℕ) : ℝ)) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [term, Nat.ne_of_gt hm]
    · simp only [term, hk, ↓reduceIte]
      rw [mul_left_comm, ← Real.exp_add]
      congr 1
      push_cast
      ring
  have hle : ∀ k : ℕ, term (m - 1) s (k + 1) ≤
      term m s (k + 1) - Real.exp (-s) * term m s k := by
    intro k
    rw [hshift]
    simpa [term, Nat.succ_ne_zero, sub_mul] using
      mul_le_mul_of_nonneg_right (power_increment m k hm)
        (Real.exp_pos (-s * ((k + 1 : ℕ) : ℝ))).le
  have hb' : Summable (fun k : ℕ => term (m - 1) s (k + 1)) :=
    (summable_nat_add_iff 1).2 hb
  have h := hb'.tsum_le_tsum hle (hc.sub (ha.mul_left (Real.exp (-s))))
  have hsum' : (∑' k : ℕ, term (m - 1) s (k + 1)) = powerSum (m - 1) s := by
    simpa [powerSum, term] using hb.tsum_eq_zero_add
  rw [hsum', Summable.tsum_sub hc (ha.mul_left _), hsum, tsum_mul_left] at h
  change powerSum (m - 1) s ≤ powerSum m s - Real.exp (-s) * powerSum m s at h
  nlinarith

theorem normalized_power_perturbation_all_cutoff_kl
    (m : ℕ) (hm : 4 ≤ m)
    (d : ℕ → ℝ) (hd0 : d 0 = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hd : ∀ k : ℕ, 0 < k →
      0 ≤ d k ∧ d k ≤ δ * (k : ℝ) ^ (m - 1))
    (s : ℝ) (hs : 0 < s)
    (hZ : (m.factorial : ℝ) / 2 ≤
      s ^ (m + 1) * powerSum m s) :
    let v : Bool → ℕ → ℝ := fun i k =>
      term m s k + if i then d k * Real.exp (-s * (k : ℝ)) else 0
    let Z : Bool → ℝ := fun i => ∑' k : ℕ, v i k
    let p : Bool → ℕ → ℝ := fun i k => v i k / Z i
    let w : ℕ → ℝ := fun k => p true k - p false k
    (∀ i : Bool, HasSum (p i) 1 ∧ p i 0 = 0 ∧
      ∀ k : ℕ, 0 < k → 0 < p i k) ∧
    (∀ j : Bool,
      Summable (fun k : ℕ => (w k) ^ 2 / p j k) ∧
      (∑' k : ℕ, (w k) ^ 2 / p j k) ≤
        4 * δ ^ 2 * (1 - Real.exp (-s)) ^ 2) ∧
    (∀ i : Bool,
      Summable (fun k : ℕ => p i k * Real.log (p i k / p (!i) k)) ∧
      (∑' k : ℕ, p i k * Real.log (p i k / p (!i) k)) ≤
        ∑' k : ℕ, (w k) ^ 2 / p (!i) k) ∧
    (∀ L : ℕ, 1 ≤ L →
      let a : Bool → Option (Fin L) → ℝ := fun i z =>
        match z with
        | some r => p i (r.val + 1)
        | none => 1 - ∑ r : Fin L, p i (r.val + 1)
      ∀ i : Bool,
        klDivergence (a i) (a (!i)) ≤
          4 * δ ^ 2 * s ^ 2 * min 1 ((s * (L : ℝ)) ^ (m - 1))) := by
  have hAdj := adjacent_power_sum m (by omega) s hs
  have hAdj2 := adjacent_power_sum (m - 1) (by omega) s hs
  have hZpos := powerSum_pos m hs
  have hr : 0 < 1 - Real.exp (-s) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -s < 0)
    linarith
  have hTwo : powerSum (m - 2) s ≤
      (1 - Real.exp (-s)) ^ 2 * powerSum m s := by
    have he : m - 1 - 1 = m - 2 := by omega
    rw [he] at hAdj2
    nlinarith [mul_le_mul_of_nonneg_left hAdj hr.le]
  let D : ℕ → ℝ := fun k => d k * Real.exp (-s * (k : ℝ))
  have hD : ∀ k, 0 ≤ D k ∧ D k ≤ δ * term (m - 1) s k := by
    intro k
    by_cases hk : k = 0
    · simp [D, hk, hd0, term]
    · simpa [D, term, hk] using
        ⟨mul_nonneg (hd k (Nat.pos_of_ne_zero hk)).1 (Real.exp_pos _).le,
         mul_le_mul_of_nonneg_right (hd k (Nat.pos_of_ne_zero hk)).2
           (Real.exp_pos (-s * (k : ℝ))).le⟩
  have hDs : Summable D := by
    apply ((summable_term (m - 1) hs).mul_left δ).of_norm_bounded
    intro k
    simpa [Real.norm_eq_abs, abs_of_nonneg (hD k).1] using (hD k).2
  let A : ℝ := ∑' k : ℕ, D k
  have hA : 0 ≤ A := tsum_nonneg (fun k => (hD k).1)
  have hAb : A ≤ δ * powerSum (m - 1) s := by
    simpa [A, powerSum, tsum_mul_left] using
      hDs.tsum_le_tsum (fun k => (hD k).2) ((summable_term _ hs).mul_left δ)
  let v : Bool → ℕ → ℝ := fun i k => term m s k + if i then D k else 0
  let Z : Bool → ℝ := fun i => ∑' k : ℕ, v i k
  let p : Bool → ℕ → ℝ := fun i k => v i k / Z i
  let w : ℕ → ℝ := fun k => p true k - p false k
  have hvs (i : Bool) : Summable (v i) := by
    cases i
    · simpa [v] using summable_term m hs
    · simpa [v] using (summable_term m hs).add hDs
  have hZeq : Z false = powerSum m s ∧ Z true = powerSum m s + A := by
    constructor
    · simp [Z, v, powerSum]
    · simpa [Z, v, powerSum, A] using (summable_term m hs).tsum_add hDs
  have hZp (i : Bool) : 0 < Z i := by
    cases i
    · simpa [hZeq.1] using hZpos
    · rw [hZeq.2]
      positivity
  have hvn (i : Bool) (k : ℕ) : 0 ≤ v i k := by
    cases i <;> simp only [v, Bool.false_eq_true, ↓reduceIte, add_zero]
    · exact term_nonneg _ _ _
    · exact add_nonneg (term_nonneg _ _ _) (hD k).1
  have hvp (i : Bool) (k : ℕ) (hk : 0 < k) : 0 < v i k := by
    have ht : 0 < term m s k := by
      simp only [term, Nat.ne_of_gt hk, ↓reduceIte]
      positivity
    cases i <;> simp only [v, Bool.false_eq_true, ↓reduceIte, add_zero]
    · exact ht
    · exact add_pos_of_pos_of_nonneg ht (hD k).1
  have hprob (i : Bool) : HasSum (p i) 1 ∧ p i 0 = 0 ∧
      ∀ k : ℕ, 0 < k → 0 < p i k := by
    constructor
    · convert (hvs i).hasSum.div_const (Z i) using 1
      exact (div_self (hZp i).ne').symm
    constructor
    · cases i <;> simp [p, v, D, hd0, term]
    · intro k hk
      exact div_pos (hvp i k hk) (hZp i)
  let ε : ℝ := A / powerSum m s
  have hε0 : 0 ≤ ε := div_nonneg hA hZpos.le
  have hε : ε ≤ δ * (1 - Real.exp (-s)) := by
    apply (div_le_iff₀ hZpos).2
    exact hAb.trans (by nlinarith [mul_le_mul_of_nonneg_left hAdj hδ])
  have hDrift (k : ℕ) :
      w k = (D k - ε * term m s k) / Z true := by
    have he : Z true = (1 + ε) * powerSum m s := by
      dsimp [ε]
      rw [hZeq.2]
      field_simp
      <;> ring
    dsimp [w, p, v]
    simp only [↓reduceIte, add_zero]
    rw [hZeq.1]
    dsimp [ε]
    rw [hZeq.2]
    field_simp
    <;> ring
  change (∀ i : Bool, HasSum (p i) 1 ∧ p i 0 = 0 ∧
      ∀ k : ℕ, 0 < k → 0 < p i k) ∧
    (∀ j : Bool, Summable (fun k : ℕ => (w k) ^ 2 / p j k) ∧
      (∑' k : ℕ, (w k) ^ 2 / p j k) ≤
        4 * δ ^ 2 * (1 - Real.exp (-s)) ^ 2) ∧
    (∀ i : Bool,
      Summable (fun k : ℕ => p i k * Real.log (p i k / p (!i) k)) ∧
      (∑' k : ℕ, p i k * Real.log (p i k / p (!i) k)) ≤
        ∑' k : ℕ, (w k) ^ 2 / p (!i) k) ∧
    (∀ L : ℕ, 1 ≤ L →
      let a : Bool → Option (Fin L) → ℝ := fun i z =>
        match z with
        | some r => p i (r.val + 1)
        | none => 1 - ∑ r : Fin L, p i (r.val + 1)
      ∀ i : Bool, klDivergence (a i) (a (!i)) ≤
        4 * δ ^ 2 * s ^ 2 * min 1 ((s * (L : ℝ)) ^ (m - 1)))
  refine ⟨hprob, ?_, ?_, ?_⟩
  · intro j
    let E : ℕ → ℝ := fun k =>
      (2 * δ ^ 2 * term (m - 2) s k +
        2 * (δ * (1 - Real.exp (-s))) ^ 2 * term m s k) / powerSum m s
    have hEs : Summable E :=
      (((summable_term (m - 2) hs).mul_left (2 * δ ^ 2)).add
        ((summable_term m hs).mul_left (2 * (δ * (1 - Real.exp (-s))) ^ 2))).div_const _
    have hEn (k : ℕ) : 0 ≤ E k := by
      dsimp [E]
      exact div_nonneg (add_nonneg
        (mul_nonneg (by positivity) (term_nonneg _ _ _))
        (mul_nonneg (by positivity) (term_nonneg _ _ _))) hZpos.le
    have hPoint (k : ℕ) : (w k) ^ 2 / p j k ≤ E k := by
      by_cases hk : k = 0
      · subst k
        have hz := (hprob j).2.1
        have hz0 := (hprob false).2.1
        have hz1 := (hprob true).2.1
        simp [w, hz, hz0, hz1, E, term]
      have ht : 0 < term m s k := by
        simp only [term, hk, ↓reduceIte]
        positivity
      have hvle : term m s k ≤ v j k := by
        cases j <;> simp only [v, Bool.false_eq_true, ↓reduceIte, add_zero]
        · exact le_rfl
        · exact le_add_of_nonneg_right (hD k).1
      have hZZ : Z j ≤ Z true := by
        cases j
        · rw [hZeq.1, hZeq.2]; exact le_add_of_nonneg_right hA
        · exact le_rfl
      have hZ01 : powerSum m s ≤ Z true := by
        rw [hZeq.2]; exact le_add_of_nonneg_right hA
      have hDen : powerSum m s * term m s k * Z j ≤
          Z true ^ 2 * v j k := by
        calc
          powerSum m s * term m s k * Z j ≤
              Z true * term m s k * Z true :=
            mul_le_mul (mul_le_mul_of_nonneg_right hZ01 ht.le) hZZ
              (hZp j).le (by positivity)
          _ ≤ Z true ^ 2 * v j k := by
            nlinarith [mul_le_mul_of_nonneg_left hvle (sq_nonneg (Z true))]
      have hNorm : (w k) ^ 2 / p j k ≤
          (D k - ε * term m s k) ^ 2 / (powerSum m s * term m s k) := by
        rw [hDrift]
        dsimp only [p]
        apply (div_le_div_iff₀ (div_pos (hvp j k (Nat.pos_of_ne_zero hk)) (hZp j))
          (mul_pos hZpos ht)).2
        apply (div_le_iff₀ (hZp j)).2
        rw [div_pow]
        apply (div_le_iff₀ (sq_pos_of_pos (hZp true))).2
        nlinarith [mul_le_mul_of_nonneg_left hDen
          (sq_nonneg (D k - ε * term m s k))]
      have hId : (δ * term (m - 1) s k) ^ 2 =
          δ ^ 2 * term (m - 2) s k * term m s k := by
        have he : m = (m - 2) + 2 := by omega
        have he' : m - 1 = (m - 2) + 1 := by omega
        simp only [term, hk, ↓reduceIte]
        rw [he', he]
        ring
      have hDsq : (D k) ^ 2 ≤ δ ^ 2 * term (m - 2) s k * term m s k := by
        rw [← hId]
        exact pow_le_pow_left₀ (hD k).1 (hD k).2 2
      have hεsq := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hε0 hε 2) (sq_nonneg (term m s k))
      have hNum : (D k - ε * term m s k) ^ 2 ≤
          (2 * δ ^ 2 * term (m - 2) s k +
            2 * (δ * (1 - Real.exp (-s))) ^ 2 * term m s k) * term m s k := by
        nlinarith [sq_nonneg (D k + ε * term m s k)]
      apply hNorm.trans
      dsimp only [E]
      apply (div_le_div_iff₀ (mul_pos hZpos ht) hZpos).2
      nlinarith [mul_le_mul_of_nonneg_left hNum hZpos.le]
    have hEnergySummable : Summable (fun k : ℕ => (w k) ^ 2 / p j k) := by
      apply hEs.of_norm_bounded
      intro k
      have hp : 0 ≤ p j k := div_nonneg (hvn j k) (hZp j).le
      simpa [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp)] using hPoint k
    refine ⟨hEnergySummable, (hEnergySummable.tsum_le_tsum hPoint hEs).trans ?_⟩
    have hSumE : (∑' k : ℕ, E k) =
        (2 * δ ^ 2 * powerSum (m - 2) s +
          2 * (δ * (1 - Real.exp (-s))) ^ 2 * powerSum m s) / powerSum m s := by
      dsimp [E]
      rw [tsum_div_const, Summable.tsum_add
        ((summable_term (m - 2) hs).mul_left _)
        ((summable_term m hs).mul_left _), tsum_mul_left, tsum_mul_left]
      rfl
    rw [hSumE]
    apply (div_le_iff₀ hZpos).2
    nlinarith [mul_le_mul_of_nonneg_left hTwo (by positivity : 0 ≤ 2 * δ ^ 2)]
  · intro i
    sorry
  · intro L hL
    sorry

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution
