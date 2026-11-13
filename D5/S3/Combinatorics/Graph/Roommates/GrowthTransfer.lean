/- GID: D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/GrowthTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Subadditive]
   utility: none
   digest: Uniform same-base exponential bounds for the literal range-two source probability. -/

import D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer
open Set Filter
open scoped Topology

/-- The two Fekete applications turn a bounded additive defect into all-length bounds.
This lemma is an internal component of the full certificate-count route. -/
theorem additive_defect_bounds (f : ℕ → ℝ) (D : ℝ)
    (hzero : f 0 = 0) (hnonneg : ∀ n, 0 ≤ f n) (hD : 0 ≤ D)
    (hsub : Subadditive f) (hrev : ∀ n m, f n + f m ≤ f (n + m) + D) :
    ∃ h : ℝ, 0 ≤ h ∧ Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 h) ∧
      ∀ n, h * n ≤ f n ∧ f n ≤ h * n + D := by
  have hb : BddBelow (range (fun n => f n / (n : ℝ))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)⟩
  let h := hsub.lim
  have ht : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 h) := hsub.tendsto_lim hb
  have hpos : 0 ≤ h := ge_of_tendsto ht (Eventually.of_forall fun n =>
    div_nonneg (hnonneg n) (Nat.cast_nonneg n))
  let u : ℕ → ℝ := fun n => -f n + D
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [hrev n m]
  have hlin (n : ℕ) : f n ≤ (n : ℝ) * f 1 := by
    have hh := hsub.apply_mul_add_le n 1 0
    simpa [hzero] using hh
  have hub : BddBelow (range (fun n => u n / (n : ℝ))) := by
    refine ⟨-f 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (hnonneg 1)
    · apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      dsimp [u]
      linarith [hlin n]
  have huT : Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 (-h)) := by
    have hd : Tendsto (fun n : ℕ => D / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hh := ht.neg.add hd
    simpa only [u, add_div, neg_div, add_zero] using hh
  have hulim : hu.lim = -h := tendsto_nhds_unique (hu.tendsto_lim hub) huT
  refine ⟨h, hpos, ht, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, hzero, hD]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  constructor
  · exact (le_div_iff₀ hnR).mp (hsub.lim_le_div hb hn)
  · have hh := hu.lim_le_div hub hn
    rw [hulim] at hh
    have hh' := (le_div_iff₀ hnR).mp hh
    dsimp [u] at hh'
    nlinarith

/-- A fixed gap can be absorbed as a bounded logarithmic defect, with no parity premise. -/
theorem fixed_gap_log_bounds (f : ℕ → ℝ) (g : ℕ)
    (hzero : f 0 = 0) (hnonneg : ∀ n, 0 ≤ f n)
    (hsub : Subadditive f)
    (hpad : ∀ n m, 0 < n → 0 < m → f n + f m ≤ f (n + m + g)) :
    ∃ h : ℝ, 0 ≤ h ∧ Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 h) ∧
      ∀ n, h * n ≤ f n ∧ f n ≤ h * n + f g := by
  apply additive_defect_bounds f (f g) hzero hnonneg (hnonneg g) hsub
  intro n m
  by_cases hn : n = 0
  · simp [hn, hzero, hnonneg g]
  by_cases hm : m = 0
  · simp [hm, hzero, hnonneg g]
  exact (hpad n m (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm)).trans (hsub _ _)

#print axioms additive_defect_bounds
#print axioms fixed_gap_log_bounds

open OpenCertificates

/-- Conditional analytic consumer for the exact labelled-profile probability.
The hypotheses are count-level concatenation, closure, and a strict three-site
bound. They are not a proof of those combinatorial obligations. The source uses
N = n+5, so the conclusion covers both parities at every N ≥ 7. -/
theorem same_q_probability_of_counts
    (hpad : ∀ m k : ℕ, 0 < m → 0 < k → count m * count k ≤ count (m + k + 6))
    (hclose : ∀ m : ℕ, 0 < m → count m ≤
      Fintype.card {p : SourceModel.Profile (m + 1) // SourceModel.HasStableMatching p})
    (hstrict : count 3 < 24 ^ 3) :
    ∃ q c C : ℝ, 0 < q ∧ q < 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        c * q ^ (n + 5) ≤ SourceModel.solutionProbability n ∧
        SourceModel.solutionProbability n ≤ C * q ^ (n + 5) := by
  have hcposN (m : ℕ) : 0 < count m :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 6) m) (count_lower m)
  have hcpos (m : ℕ) : (0 : ℝ) < count m := by exact_mod_cast hcposN m
  have hcone (m : ℕ) : (1 : ℝ) ≤ count m := by
    exact_mod_cast (Nat.succ_le_iff.mpr (hcposN m))
  have hc0 : count 0 = 1 := by
    have hu : count 0 ≤ 1 := by
      calc
        count 0 ≤ Fintype.card (Word 0) :=
          Fintype.card_le_of_injective (fun w : CertifiedWord 0 => w.val)
            (fun _ _ h => Subtype.ext h)
        _ = 1 := by simp [Word]
    have hl := hcposN 0
    omega
  let f : ℕ → ℝ := fun m => Real.log (count m)
  have hf0 : f 0 = 0 := by simp [f, hc0]
  have hfnonneg (m : ℕ) : 0 ≤ f m := Real.log_nonneg (hcone m)
  have hfsub : Subadditive f := by
    intro m k
    have hu : (count (m + k) : ℝ) ≤ (count m : ℝ) * count k := by
      exact_mod_cast count_submultiplicative m k
    have hh := Real.log_le_log (hcpos (m + k)) hu
    simpa only [f, Real.log_mul (ne_of_gt (hcpos m)) (ne_of_gt (hcpos k))] using hh
  have hfpad : ∀ m k : ℕ, 0 < m → 0 < k → f m + f k ≤ f (m + k + 6) := by
    intro m k hm hk
    have hl : (count m : ℝ) * count k ≤ (count (m + k + 6) : ℝ) := by
      exact_mod_cast hpad m k hm hk
    have hh := Real.log_le_log (mul_pos (hcpos m) (hcpos k)) hl
    simpa only [f, Real.log_mul (ne_of_gt (hcpos m)) (ne_of_gt (hcpos k))] using hh
  obtain ⟨h, _, _, hb⟩ :=
    GrowthTransfer.fixed_gap_log_bounds f 6 hf0 hfnonneg hfsub hfpad
  have hlt : h < Real.log 24 := by
    have hh := (hb 3).1
    have hs : Real.log (count 3 : ℝ) < Real.log ((24 : ℝ) ^ 3) :=
      Real.log_lt_log (hcpos 3) (by exact_mod_cast hstrict)
    rw [Real.log_pow] at hs
    dsimp [f] at hh
    norm_num only [Nat.cast_ofNat] at hh hs
    linarith
  have hexp (m : ℕ) : Real.exp (h * m) = Real.exp h ^ m := by
    rw [mul_comm, Real.exp_nat_mul]
  have hgrowth (m : ℕ) : Real.exp h ^ m ≤ (count m : ℝ) ∧
      (count m : ℝ) ≤ Real.exp h ^ m * count 6 := by
    constructor
    · have hh := Real.exp_le_exp.mpr (hb m).1
      simpa only [f, hexp, Real.exp_log (hcpos m)] using hh
    · have hh := Real.exp_le_exp.mpr (hb m).2
      simpa only [f, Real.exp_add, hexp, Real.exp_log (hcpos m),
        Real.exp_log (hcpos 6)] using hh
  have hepos : 0 < Real.exp h := Real.exp_pos h
  have helt : Real.exp h < 24 := by
    calc
      Real.exp h < Real.exp (Real.log 24) := Real.exp_lt_exp.mpr hlt
      _ = 24 := Real.exp_log (by norm_num)
  refine ⟨Real.exp h / 24, 1 / Real.exp h ^ 6, count 6,
    div_pos hepos (by norm_num), (div_lt_one (by norm_num)).mpr helt,
    one_div_pos.mpr (pow_pos hepos 6), hcpos 6, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hclose' := hclose m (by omega)
  have hpows : Real.exp h ^ (m + 1 + 5) = Real.exp h ^ m * Real.exp h ^ 6 := by
    rw [← pow_add, show m + 6 = m + 1 + 5 by omega]
  have hlower : (1 / Real.exp h ^ 6) * (Real.exp h / 24) ^ (m + 1 + 5) =
      Real.exp h ^ m / (24 : ℝ) ^ (m + 1 + 5) := by
    rw [div_pow, hpows]
    field_simp [ne_of_gt hepos]
  constructor
  · rw [hlower, CyclicClosure.source_probability_eq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (hgrowth m).1.trans (by exact_mod_cast hclose')
  · calc
      SourceModel.solutionProbability (m + 1) ≤
          (count (m + 1 + 5) : ℝ) / (24 : ℝ) ^ (m + 1 + 5) :=
        CyclicClosure.source_probability_le_open_proportion (m + 1)
      _ ≤ (Real.exp h ^ (m + 1 + 5) * count 6) / (24 : ℝ) ^ (m + 1 + 5) :=
        div_le_div_of_nonneg_right (hgrowth (m + 1 + 5)).2 (by positivity)
      _ = (count 6 : ℝ) * (Real.exp h / 24) ^ (m + 1 + 5) := by rw [div_pow]; ring

#print axioms same_q_probability_of_counts

/-- The exact d=1, r=2 specialization of Mertens's probability conjecture.
There are no combinatorial or analytic premises. The source parameter is
N=n+5; all N≥7, including both parities, satisfy the bounds for the same q.
The probability counts labelled ranking profiles admitting a stable partial
matching, with singles permitted, once per profile. -/
theorem result :
    ∃ q c C : ℝ, 0 < q ∧ q < 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        c * q ^ (n + 5) ≤ SourceModel.solutionProbability n ∧
        SourceModel.solutionProbability n ≤ C * q ^ (n + 5) := by
  apply same_q_probability_of_counts
  · exact fun m k _ _ => PaddedCompletion.count_padded_supermultiplicative m k
  · exact fun m _ => CyclicClosure.count_le_successful_profile_count m
  · exact lt_of_le_of_lt OpenCertificates.count_three_bound (by norm_num)

#print axioms result

end D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer
