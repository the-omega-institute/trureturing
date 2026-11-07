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

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27700 -/

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
  push_cast at hp hh ⊢
  nlinarith only [hh]

private lemma adjacent_power_sum (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) (hs : 0 < s) :
    powerSum (m - 1) s ≤ (1 - Real.exp (-s)) * powerSum m s := by
  have ha := summable_term m hs
  have hb := summable_term (m - 1) hs
  have hc : Summable (fun k : ℕ => term m s (k + 1)) :=
    (summable_nat_add_iff 1).2 ha
  have hsum : (∑' k : ℕ, term m s (k + 1)) = powerSum m s := by
    simpa [powerSum, term] using ha.tsum_eq_zero_add.symm
  have hshift : ∀ k : ℕ,
      Real.exp (-s) * term m s k =
        (k : ℝ) ^ m * Real.exp (-s * ((k + 1 : ℕ) : ℝ)) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [term, Nat.ne_of_gt hm]
    · simp only [term, hk, ↓reduceIte]
      rw [show -s * ((k + 1 : ℕ) : ℝ) = -s + -s * (k : ℝ) by
        push_cast
        ring, Real.exp_add]
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
    simpa [powerSum, term] using hb.tsum_eq_zero_add.symm
  rw [hsum', Summable.tsum_sub hc (ha.mul_left _), hsum, tsum_mul_left] at h
  change powerSum (m - 1) s ≤ powerSum m s - Real.exp (-s) * powerSum m s at h
  nlinarith

private lemma normalized_power_perturbation_energy
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
        4 * δ ^ 2 * (1 - Real.exp (-s)) ^ 2) := by
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
    · constructor
      · exact mul_nonneg (hd k (Nat.pos_of_ne_zero hk)).1 (Real.exp_pos _).le
      · calc
          D k ≤ (δ * (k : ℝ) ^ (m - 1)) * Real.exp (-s * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (hd k (Nat.pos_of_ne_zero hk)).2 (Real.exp_pos _).le
          _ = δ * term (m - 1) s k := by simp [term, hk, mul_assoc]
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
        4 * δ ^ 2 * (1 - Real.exp (-s)) ^ 2)
  refine ⟨hprob, ?_⟩
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
              (hZp j).le (mul_nonneg (hZp true).le ht.le)
          _ ≤ Z true ^ 2 * v j k := by
            nlinarith [mul_le_mul_of_nonneg_left hvle (sq_nonneg (Z true))]
      have hNorm : (w k) ^ 2 / p j k ≤
          (D k - ε * term m s k) ^ 2 / (powerSum m s * term m s k) := by
        calc
          (w k) ^ 2 / p j k =
              (D k - ε * term m s k) ^ 2 * Z j / (Z true ^ 2 * v j k) := by
            rw [hDrift]
            dsimp only [p]
            field_simp
          _ ≤ (D k - ε * term m s k) ^ 2 /
              (powerSum m s * term m s k) := by
            apply (div_le_div_iff₀
              (mul_pos (sq_pos_of_pos (hZp true)) (hvp j k (Nat.pos_of_ne_zero hk)))
              (mul_pos hZpos ht)).2
            nlinarith only [mul_le_mul_of_nonneg_left hDen
              (sq_nonneg (D k - ε * term m s k))]
      have hId : (δ * term (m - 1) s k) ^ 2 =
          δ ^ 2 * term (m - 2) s k * term m s k := by
        have he : m = (m - 2) + 2 := by omega
        have he' : m - 1 = (m - 2) + 1 := by omega
        simp only [term, hk, ↓reduceIte]
        have hp1 : (k : ℝ) ^ (m - 1) = (k : ℝ) ^ (m - 2) * (k : ℝ) := by
          rw [he', pow_succ]
        have hp2 : (k : ℝ) ^ m = (k : ℝ) ^ (m - 2) * (k : ℝ) ^ 2 := by
          calc
            (k : ℝ) ^ m = (k : ℝ) ^ ((m - 2) + 2) := congrArg (fun n => (k : ℝ) ^ n) he
            _ = _ := pow_add _ _ _
        rw [hp1, hp2]
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
      simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp)] using hPoint k
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

private lemma countable_kl_le_energy {ι : Type*}
    (p q : ι → ℝ) (hp : HasSum p 1) (hq : HasSum q 1)
    (hpos : ∀ k, (p k = 0 ∧ q k = 0) ∨ (0 < p k ∧ 0 < q k))
    (he : Summable (fun k => (p k - q k) ^ 2 / q k)) :
    Summable (fun k => p k * Real.log (p k / q k)) ∧
      (∑' k, p k * Real.log (p k / q k)) ≤
        ∑' k, (p k - q k) ^ 2 / q k := by
  have hbounds (k : ι) :
      p k - q k ≤ p k * Real.log (p k / q k) ∧
      p k * Real.log (p k / q k) ≤
        p k - q k + (p k - q k) ^ 2 / q k := by
    rcases hpos k with h | h
    · simp [h.1, h.2]
    have hratio := div_pos h.1 h.2
    have hu := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos hratio) h.1.le
    have hl := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos hratio) h.1.le
    have hid : p k * (p k / q k - 1) =
        p k - q k + (p k - q k) ^ 2 / q k := by
      field_simp
      <;> ring
    have hid' : p k * (1 - (p k / q k)⁻¹) = p k - q k := by
      field_simp
    exact ⟨hid' ▸ hl, hid ▸ hu⟩
  have hn (k : ι) : 0 ≤ p k ∧ 0 ≤ q k := by
    rcases hpos k with h | h
    · simp [h.1, h.2]
    · exact ⟨h.1.le, h.2.le⟩
  have hs : Summable (fun k => p k * Real.log (p k / q k)) := by
    apply ((hp.summable.add hq.summable).add he).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_le]
    have he0 : 0 ≤ (p k - q k) ^ 2 / q k := div_nonneg (sq_nonneg _) (hn k).2
    constructor <;> linarith [(hbounds k).1, (hbounds k).2, (hn k).1, (hn k).2]
  refine ⟨hs, ?_⟩
  have h := hs.tsum_le_tsum (fun k => (hbounds k).2)
    ((hp.summable.sub hq.summable).add he)
  simpa only [Summable.tsum_add (hp.summable.sub hq.summable) he,
    (hp.sub hq).tsum_eq, sub_self, zero_add] using h

private lemma countable_weighted_cauchy (f g : ℕ → ℝ)
    (hf : Summable f) (hg : Summable g) (hgp : ∀ k, 0 < g k)
    (he : Summable (fun k => (f k) ^ 2 / g k)) :
    (∑' k, f k) ^ 2 ≤ (∑' k, g k) * ∑' k, (f k) ^ 2 / g k := by
  apply le_of_tendsto_of_tendsto (hf.hasSum.tendsto_sum_nat.pow 2)
    (hg.hasSum.tendsto_sum_nat.mul he.hasSum.tendsto_sum_nat)
  exact Filter.Eventually.of_forall (fun n =>
    sum_sq_le_sum_mul_sum_of_sq_le_mul (range n)
      (fun k _ => (hgp k).le)
      (fun k _ => div_nonneg (sq_nonneg _) (hgp k).le)
      (fun k _ => by rw [mul_div_cancel₀ _ (hgp k).ne']))

private lemma split_positive_series (f : ℕ → ℝ) (hf : Summable f)
    (hf0 : f 0 = 0) (L : ℕ) :
    (∑ r : Fin L, f (r.val + 1)) + (∑' k : ℕ, f (k + L + 1)) = ∑' k, f k := by
  have h := ((summable_nat_add_iff 1).2 hf).sum_add_tsum_nat_add L
  rw [hf.tsum_eq_zero_add, hf0, zero_add]
  simpa only [Nat.add_assoc, Fin.sum_univ_eq_sum_range] using h

private lemma collapsed_kl_bounds
    (p q : ℕ → ℝ) (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : p 0 = 0) (hq0 : q 0 = 0)
    (hpp : ∀ k, 0 < k → 0 < p k) (hqp : ∀ k, 0 < k → 0 < q k)
    (he : Summable (fun k => (p k - q k) ^ 2 / q k)) (L : ℕ) :
    let a : Option (Fin L) → ℝ := fun z => match z with
      | some r => p (r.val + 1)
      | none => 1 - ∑ r : Fin L, p (r.val + 1)
    let b : Option (Fin L) → ℝ := fun z => match z with
      | some r => q (r.val + 1)
      | none => 1 - ∑ r : Fin L, q (r.val + 1)
    klDivergence a b ≤ ∑' k, (p k - q k) ^ 2 / q k ∧
    ((∑ r : Fin L, q (r.val + 1)) ≤ 1 / 2 →
      klDivergence a b ≤ 2 * ∑ r : Fin L,
        (p (r.val + 1) - q (r.val + 1)) ^ 2 / q (r.val + 1)) := by
  classical
  let a : Option (Fin L) → ℝ := fun z => match z with
    | some r => p (r.val + 1)
    | none => 1 - ∑ r : Fin L, p (r.val + 1)
  let b : Option (Fin L) → ℝ := fun z => match z with
    | some r => q (r.val + 1)
    | none => 1 - ∑ r : Fin L, q (r.val + 1)
  let E : ℕ → ℝ := fun k => (p k - q k) ^ 2 / q k
  have hE0 : E 0 = 0 := by simp [E, hp0, hq0]
  have htail (f : ℕ → ℝ) (hf : HasSum f 1) (hf0 : f 0 = 0)
      (hfp : ∀ k, 0 < k → 0 < f k) :
      (1 - ∑ r : Fin L, f (r.val + 1)) = ∑' k : ℕ, f (k + L + 1) ∧
      0 < 1 - ∑ r : Fin L, f (r.val + 1) := by
    have ht := split_positive_series f hf.summable hf0 L
    rw [hf.tsum_eq] at ht
    have hp' : 0 < ∑' k : ℕ, f (k + L + 1) :=
      ((summable_nat_add_iff (L + 1)).2 hf.summable).tsum_pos
        (fun k => (hfp _ (by omega)).le) 0 (hfp _ (by omega))
    constructor <;> linarith
  have hpt := htail p hp hp0 hpp
  have hqt := htail q hq hq0 hqp
  have hap (z : Option (Fin L)) : 0 < a z := by
    cases z with
    | none => exact hpt.2
    | some r => exact hpp _ (by omega)
  have hbp (z : Option (Fin L)) : 0 < b z := by
    cases z with
    | none => exact hqt.2
    | some r => exact hqp _ (by omega)
  have ha : HasSum a 1 := by
    rw [hasSum_fintype]
    simp only [Fintype.sum_option, a]
    ring
  have hb : HasSum b 1 := by
    rw [hasSum_fintype]
    simp only [Fintype.sum_option, b]
    ring
  have hkl := (countable_kl_le_energy a b ha hb
    (fun z => Or.inr ⟨hap z, hbp z⟩) (summable_fintype _)).2
  change klDivergence a b ≤ _ ∧ _
  change klDivergence a b ≤ ∑' z, (a z - b z) ^ 2 / b z at hkl
  rw [tsum_fintype, Fintype.sum_option] at hkl
  let S : ℝ := ∑ r : Fin L, E (r.val + 1)
  let π : ℝ := ∑ r : Fin L, q (r.val + 1)
  have hSn : 0 ≤ S := sum_nonneg (fun r _ => div_nonneg (sq_nonneg _) (hqp _ (by omega)).le)
  have hsum : (∑ r : Fin L, (p (r.val + 1) - q (r.val + 1))) =
      (∑ r : Fin L, p (r.val + 1)) - π := by simp [π, sum_sub_distrib]
  have hc := countable_weighted_cauchy
    (fun k => p (k + L + 1) - q (k + L + 1)) (fun k => q (k + L + 1))
    (((summable_nat_add_iff (L + 1)).2 hp.summable).sub
      ((summable_nat_add_iff (L + 1)).2 hq.summable))
    ((summable_nat_add_iff (L + 1)).2 hq.summable)
    (fun k => hqp _ (by omega)) ((summable_nat_add_iff (L + 1)).2 he)
  have htd : (a none - b none) ^ 2 / b none ≤ ∑' k, E (k + L + 1) := by
    apply (div_le_iff₀ hqt.2).2
    rw [Summable.tsum_sub ((summable_nat_add_iff (L + 1)).2 hp.summable)
      ((summable_nat_add_iff (L + 1)).2 hq.summable), ← hpt.1, ← hqt.1] at hc
    simpa only [a, b, mul_comm] using hc
  constructor
  · have hsplit := split_positive_series E he hE0 L
    calc
      klDivergence a b ≤ S + (a none - b none) ^ 2 / b none := by
        simpa only [a, b, E, S, add_comm] using hkl
      _ ≤ S + ∑' k, E (k + L + 1) := add_le_add_left htd S
      _ = ∑' k, E k := hsplit
  · intro hπ
    have hc' := sum_sq_le_sum_mul_sum_of_sq_le_mul (s := univ)
      (r := fun r : Fin L => p (r.val + 1) - q (r.val + 1))
      (f := fun r : Fin L => q (r.val + 1))
      (g := fun r : Fin L => E (r.val + 1))
      (fun r _ => (hqp _ (by omega)).le)
      (fun r _ => div_nonneg (sq_nonneg _) (hqp _ (by omega)).le)
      (fun r _ => by dsimp [E]; rw [mul_div_cancel₀ _ (hqp _ (by omega)).ne'])
    have hc'' : (a none - b none) ^ 2 ≤ π * S := by
      dsimp only [a, b]
      rw [hsum] at hc'
      dsimp only [π, S] at *
      nlinarith only [hc']
    have htailbound : (a none - b none) ^ 2 / b none ≤ S := by
      apply (div_le_iff₀ hqt.2).2
      change _ ≤ S * (1 - π)
      have hπ' : π ≤ 1 / 2 := hπ
      nlinarith [mul_le_mul_of_nonneg_right hπ' hSn]
    have hkl' : klDivergence a b ≤ S + (a none - b none) ^ 2 / b none := by
      simpa only [a, b, E, S, add_comm] using hkl
    change klDivergence a b ≤ 2 * S
    linarith

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
  classical
  let v : Bool → ℕ → ℝ := fun i k =>
    term m s k + if i then d k * Real.exp (-s * (k : ℝ)) else 0
  let Z : Bool → ℝ := fun i => ∑' k : ℕ, v i k
  let p : Bool → ℕ → ℝ := fun i k => v i k / Z i
  let w : ℕ → ℝ := fun k => p true k - p false k
  change (∀ i : Bool, HasSum (p i) 1 ∧ p i 0 = 0 ∧
      ∀ k : ℕ, 0 < k → 0 < p i k) ∧
    (∀ j : Bool, Summable (fun k : ℕ => (w k) ^ 2 / p j k) ∧
      (∑' k : ℕ, (w k) ^ 2 / p j k) ≤
        4 * δ ^ 2 * (1 - Real.exp (-s)) ^ 2) ∧
    (∀ i : Bool,
      Summable (fun k : ℕ => p i k * Real.log (p i k / p (!i) k)) ∧
      (∑' k : ℕ, p i k * Real.log (p i k / p (!i) k)) ≤
        ∑' k : ℕ, (w k) ^ 2 / p (!i) k) ∧ _
  have hEnergy := normalized_power_perturbation_energy m hm d hd0 δ hδ hδ1 hd s hs hZ
  refine ⟨hEnergy.1, hEnergy.2, ?_, by sorry⟩
  intro i
  have heq : ∀ k : ℕ, (p i k - p (!i) k) ^ 2 = (w k) ^ 2 := by
    intro k
    cases i <;> simp only [Bool.not_false, Bool.not_true, w] <;> ring
  have h := countable_kl_le_energy (p i) (p (!i)) (hEnergy.1 i).1 (hEnergy.1 (!i)).1
    (fun k => by
      by_cases hk : k = 0
      · exact Or.inl ⟨hk ▸ (hEnergy.1 i).2.1, hk ▸ (hEnergy.1 (!i)).2.1⟩
      · exact Or.inr ⟨(hEnergy.1 i).2.2 k (Nat.pos_of_ne_zero hk),
          (hEnergy.1 (!i)).2.2 k (Nat.pos_of_ne_zero hk)⟩)
    (by simpa only [heq] using (hEnergy.2 (!i)).1)
  simpa only [heq] using h

#print axioms countable_kl_le_energy
#print axioms normalized_power_perturbation_energy

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution
