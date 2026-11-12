/- GID: D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/GrowthTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Subadditive]
   utility: none
   digest: Uniform same-base exponential bounds for the literal range-two source probability. -/

import D5.S3.Combinatorics.Graph.Roommates.FixedGapGrowth
import D5.S3.Combinatorics.Graph.Roommates.CyclicBridge
import D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
import D5.S3.Combinatorics.Graph.Roommates.TriangleCount

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer
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
    FixedGapGrowth.fixed_gap_log_bounds f 6 hf0 hfnonneg hfsub hfpad
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
  · rw [hlower, CyclicBridge.source_probability_eq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (hgrowth m).1.trans (by exact_mod_cast hclose')
  · calc
      SourceModel.solutionProbability (m + 1) ≤
          (count (m + 1 + 5) : ℝ) / (24 : ℝ) ^ (m + 1 + 5) :=
        CyclicBridge.source_probability_le_open_proportion (m + 1)
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
  · exact lt_of_le_of_lt TriangleCount.count_three_bound (by norm_num)

#print axioms result

end D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer
