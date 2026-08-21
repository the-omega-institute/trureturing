/- GID: D5/S3/Entropy/Forgetting/DeterministicOutputEntropyRate
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/DeterministicOutputEntropyRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound deterministic output-block entropy and prove its normalized rate vanishes. -/

import D5.S3.Entropy.Forgetting.DeterministicEntropyEquality

/- Library-search audit trail (2026-08-21):
   * Repository exact hits `shannonEntropy`, `conditionalEntropy`, `pushforward`,
     `entropy_le_log_card`, `conditional_entropy_eq_zero_of_point_mass_on_support`, and
     `shannon_entropy_nonneg` provide the canonical finite entropy machinery.
   * Exact hits `pushforward_entropy_eq_iff_injective_on_support` and
     `pushforward_entropy_lt_iff_not_injective_on_support` are directly applied to obtain
     deterministic entropy nonincrease without imposing surjectivity on an output-block map.
   * Pinned Mathlib hits `tendsto_bdd_div_atTop_nhds_zero`,
     `tendsto_natCast_atTop_atTop`, and `tendsto_add_atTop_nat` close the rate limit.
   * Searches found no existing theorem carrying the five output-block clauses together. -/

namespace D5.S3.Entropy.Forgetting.DeterministicOutputEntropyRate

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.EntropyNonneg
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
open D5.S3.Entropy.MaxEntropy
open Filter

/-- The finite block of readouts from times zero through `T`, constructed from one initial state. -/
def outputBlock {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (T : ℕ) (initial : Y) : Fin (T + 1) -> O :=
  fun t => readout ((update^[t.1]) initial)

/-- The corresponding block when a sampled configuration selects the fixed update and readout. -/
def configuredOutputBlock {Theta Y O : Type*}
    (update : Theta -> Y -> Y) (readout : Theta -> Y -> O)
    (T : ℕ) (initial : Theta × Y) : Fin (T + 1) -> O :=
  fun t => readout initial.1 (((update initial.1)^[t.1]) initial.2)

private theorem pushforward_is_law {X A : Type*} [Fintype X] [Fintype A]
    (p : X -> ℝ) (f : X -> A)
    (hp : (forall x, 0 <= p x) ∧ ∑ x, p x = 1) :
    (forall a, 0 <= pushforward f p a) ∧ ∑ a, pushforward f p a = 1 := by
  classical
  constructor
  · intro a
    simp only [pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases h : f x = a <;> simp [h, hp.1 x]
  · simp only [pushforward]
    calc
      (∑ a, ∑ x, if f x = a then p x else 0) =
          ∑ x, ∑ a, if f x = a then p x else 0 := Finset.sum_comm
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x _
        simp
      _ = 1 := hp.2

private theorem pushforward_entropy_le {X A : Type*} [Fintype X] [Fintype A]
    (p : X -> ℝ) (f : X -> A)
    (hp : (forall x, 0 <= p x) ∧ ∑ x, p x = 1) :
    shannonEntropy (pushforward f p) <= shannonEntropy p := by
  by_cases hinjective : Set.InjOn f {x | p x ≠ 0}
  · exact le_of_eq
      ((pushforward_entropy_eq_iff_injective_on_support p f hp).2 hinjective)
  · exact le_of_lt
      ((pushforward_entropy_lt_iff_not_injective_on_support p f hp).2 hinjective)

private theorem graph_joint_marginal {X A B : Type*}
    [Fintype X] [Fintype B]
    (p : X -> ℝ) (f : X -> A) (g : X -> B) :
    marginal (pushforward (fun x => (f x, g x)) p) = pushforward f p := by
  classical
  funext a
  simp only [marginal, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hfa : f x = a
  · simp [hfa]
  · simp [hfa]

private theorem graph_conditional_entropy_zero {X A : Type*}
    [Fintype X] [Fintype A]
    (p : X -> ℝ) (f : X -> A) :
    conditionalEntropy (pushforward (fun x => (x, f x)) p) = 0 := by
  classical
  let joint : X × A -> ℝ := pushforward (fun x => (x, f x)) p
  apply conditional_entropy_eq_zero_of_point_mass_on_support joint
  intro x hmarginal
  have hmarginal_eq : marginal joint x = p x := by
    change marginal (pushforward (fun y => (id y, f y)) p) x = p x
    rw [graph_joint_marginal p id f]
    simp only [pushforward]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  refine ⟨f x, ?_⟩
  funext a
  rw [conditional, hmarginal_eq]
  have hpx : p x ≠ 0 := by
    intro hzero
    apply hmarginal
    rw [hmarginal_eq, hzero]
  by_cases ha : a = f x
  · subst a
    have hcell : joint (x, f x) = p x := by
      simp only [joint, pushforward]
      rw [Finset.sum_eq_single x]
      · simp
      · intro x' _ hx
        simp [hx]
      · simp
    simp [hcell, hpx]
  · have hcell : joint (x, a) = 0 := by
      simp only [joint, pushforward]
      apply Finset.sum_eq_zero
      intro x' _
      by_cases hx : x' = x
      · subst x'
        simp [Ne.symm ha]
      · simp [hx]
    simp [hcell, ha]

/-- In a finite deterministic system, every output block is fixed by its initial state, its
entropy is bounded by the initial-state budget and the log state capacity, and its entropy per
output tends to zero. The same deterministic and entropy bounds hold when a random configuration
is paired with the initial state and remains fixed throughout the block. -/
theorem deterministic_output_entropy_budget_and_rate
    {Y O Theta : Type*} [Fintype Y] [Fintype O] [Fintype Theta]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> ℝ)
    (hinitial : (forall y, 0 <= initial y) ∧ ∑ y, initial y = 1)
    (configuredUpdate : Theta -> Y -> Y) (configuredReadout : Theta -> Y -> O)
    (configuredInitial : Theta × Y -> ℝ)
    (hconfigured : (forall z, 0 <= configuredInitial z) ∧
      ∑ z, configuredInitial z = 1) :
    (forall T,
      conditionalEntropy
        (pushforward (fun y => (y, outputBlock update readout T y)) initial) = 0) ∧
    (forall T,
      shannonEntropy (pushforward (outputBlock update readout T) initial) <=
          shannonEntropy initial ∧
        shannonEntropy initial <= Real.log (Fintype.card Y)) ∧
    Tendsto
      (fun T : ℕ =>
        shannonEntropy (pushforward (outputBlock update readout T) initial) /
          ((T + 1 : ℕ) : ℝ)) atTop (nhds 0) ∧
    (forall T,
      conditionalEntropy
        (pushforward
          (fun z => (z, configuredOutputBlock configuredUpdate configuredReadout T z))
          configuredInitial) = 0) ∧
    (forall T,
      shannonEntropy
          (pushforward (configuredOutputBlock configuredUpdate configuredReadout T)
            configuredInitial) <= shannonEntropy configuredInitial) := by
  have hy_exists : ∃ y, initial y ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ∑ y, initial y = 0 := Finset.sum_eq_zero fun y _ => h y
    rw [hinitial.2] at hzero
    norm_num at hzero
  letI : Nonempty Y := ⟨hy_exists.choose⟩
  have houtput_le : forall T,
      shannonEntropy (pushforward (outputBlock update readout T) initial) <=
        shannonEntropy initial := fun T =>
    pushforward_entropy_le initial (outputBlock update readout T) hinitial
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T
    exact graph_conditional_entropy_zero initial (outputBlock update readout T)
  · intro T
    exact ⟨houtput_le T, entropy_le_log_card initial hinitial⟩
  · apply tendsto_bdd_div_atTop_nhds_zero
    · filter_upwards with T
      exact shannon_entropy_nonneg _
        (pushforward_is_law initial (outputBlock update readout T) hinitial)
    · filter_upwards with T
      exact houtput_le T
    · exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  · intro T
    exact graph_conditional_entropy_zero configuredInitial
      (configuredOutputBlock configuredUpdate configuredReadout T)
  · intro T
    exact pushforward_entropy_le configuredInitial
      (configuredOutputBlock configuredUpdate configuredReadout T) hconfigured

/-- Uniform Boolean initial states witness both probability-law hypotheses. -/
example :
    ((forall _y : Bool, 0 <= (1 / 2 : ℝ)) ∧ ∑ _y : Bool, (1 / 2 : ℝ) = 1) ∧
    ((forall _z : Unit × Bool, 0 <= (1 / 2 : ℝ)) ∧
      ∑ _z : Unit × Bool, (1 / 2 : ℝ) = 1) := by
  norm_num [Fintype.sum_bool, Fintype.sum_prod_type]

/-- The finite state domain used by the law witnesses is inhabited. -/
example : Bool := false

#print axioms deterministic_output_entropy_budget_and_rate

end D5.S3.Entropy.Forgetting.DeterministicOutputEntropyRate
