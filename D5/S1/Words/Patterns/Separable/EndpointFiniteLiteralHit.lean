/- GID: D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A fixed marked prefix transfers original-coordinate hits to finite avoiders. -/

import D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit

/-! The stream chooses one fixed prefix before the original finite permutation grows. -/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit

open ActualCycleLaw CutFactorization MinimumCutKernel EndpointCanonicalCycle
open EndpointCycleHazard EndpointFirstCycleHitLimit OccupiedComparison
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)

private theorem tendsto_firstK_of_eventual_stream_hit (e : ℤ)
    (h : ∀ᵐ ω ∂streamMeasure, ∃ k : ℕ, hit (ω k).2 (e + streamDiscrepancy k ω)) :
    Tendsto (fun k => firstKHitProbability k e) atTop (𝓝 1) := by
  let S (k : ℕ) := firstKHit k e
  have hm : Monotone S := by
    intro i j hij ω hω
    obtain ⟨k, hk, hhit⟩ := hω
    exact ⟨k, hk.trans_le hij, hhit⟩
  have hae : (⋃ k, S k) =ᵐ[streamMeasure] (Set.univ : Set Stream) := by
    filter_upwards [h] with ω hω
    obtain ⟨k, hk⟩ := hω
    exact propext (iff_of_true (Set.mem_iUnion.mpr ⟨k + 1, ⟨k, Nat.lt_succ_self k, hk⟩⟩) trivial)
  have hfull : streamMeasure (⋃ k, S k) = 1 := (measure_congr hae).trans (measure_univ : _)
  have ht := tendsto_measure_iUnion_atTop (μ := streamMeasure) hm
  rw [hfull] at ht
  simpa only [Measure.real, firstKHitProbability, ENNReal.toReal_one, Function.comp_def, S] using
    (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht

local instance (n : ℕ) : Nonempty (Avoider n) := ⟨identityAvoider n⟩

open Classical in
private theorem outer_univ (n : ℕ) :
    (uniformPmf (Avoider n)).toOuterMeasure Set.univ = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)

private theorem mass_le_one (n : ℕ) (P : Avoider n → Prop) : actualMass n P ≤ 1 := by
  classical
  unfold actualMass
  have h := (uniformPmf (Avoider n)).toOuterMeasure.mono
    (Set.subset_univ {π : Avoider n | P π})
  have h1 : (uniformPmf (Avoider n)).toOuterMeasure {π | P π} ≤ 1 :=
    h.trans_eq (outer_univ n)
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top h1

private theorem mass_mono (n : ℕ) {P Q : Avoider n → Prop} (h : ∀ π, P π → Q π) :
    actualMass n P ≤ actualMass n Q := by
  classical
  unfold actualMass
  have htop : (uniformPmf (Avoider n)).toOuterMeasure {π | Q π} ≤ 1 :=
    ((uniformPmf _).toOuterMeasure.mono (Set.subset_univ _)).trans_eq (outer_univ n)
  exact ENNReal.toReal_mono (ne_of_lt (htop.trans_lt ENNReal.one_lt_top))
    ((uniformPmf _).toOuterMeasure.mono h)

/-- Probability that the original finite avoider has a point at offset e. -/
noncomputable def literalHitProbability (e : ℤ) (n : ℕ) : ℝ :=
  actualMass n (fun π : Avoider n => hitsDiagonal π.val e)

private theorem firstKLiteral_le (k : ℕ) (e : ℤ) (n : ℕ) :
    actualMass n (actualCanonicalFirstKLiteralHit k e n) ≤ literalHitProbability e n := by
  apply mass_mono n
  rintro π ⟨p, r, _, j, _, hj⟩
  exact ⟨j, hj⟩

/-- Every fixed marked prefix supplies an eventual lower bound for the entire
finite permutation. If the stream eventually hits almost surely, the whole
finite hit probability tends to one after choosing a fixed prefix. -/
theorem finite_avoider_literal_hit_limit_of_stream_hit (e : ℤ) :
    (∀ k : ℕ, ∀ a : ℝ, a < firstKHitProbability k e →
      ∀ᶠ n in atTop, a < literalHitProbability e n) ∧
    ((∀ᵐ ω ∂streamMeasure, ∃ k : ℕ, hit (ω k).2 (e + streamDiscrepancy k ω)) →
      Tendsto (literalHitProbability e) atTop (𝓝 1)) := by
  have hp (k : ℕ) (a : ℝ) (ha : a < firstKHitProbability k e) :
      ∀ᶠ n in atTop, a < literalHitProbability e n :=
    ((tendsto_order.1 (actualCanonicalFirstKLiteralHit_limit k e)).1 a ha).mono
      fun n hn => hn.trans_le (firstKLiteral_le k e n)
  refine ⟨hp, fun h => tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro a ha
    have hk := tendsto_firstK_of_eventual_stream_hit e h
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hk).1 a ha).exists
    exact hp k a hk
  · exact fun a ha => Filter.Eventually.of_forall fun n => (mass_le_one n _).trans_lt ha

#print axioms finite_avoider_literal_hit_limit_of_stream_hit

end D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit
