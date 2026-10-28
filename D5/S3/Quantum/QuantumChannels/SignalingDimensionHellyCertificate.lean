/- GID: D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: At most binomially many inputs certify classical signaling dimension. -/

import Mathlib.Analysis.Convex.Radon
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate

/-- A channel has inputs indexing rows, with nonnegative entries and row sums one. -/
def IsChannel {α β : Type} [Fintype β] (p : α → β → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ ∀ x, ∑ y, p x y = 1

/-- Source equation for classical simulation, with shared randomness indexed by some `Fin n`. -/
def IsSimulable {α : Type} {k : ℕ} (d : ℕ) (p : α → Fin k → ℝ) : Prop :=
  ∃ n : ℕ, ∃ q : Fin n → ℝ,
    ∃ t : Fin n → α → Fin d → ℝ, ∃ r : Fin n → Fin d → Fin k → ℝ,
      (∀ l, 0 ≤ q l) ∧ (∑ l, q l = 1) ∧
      (∀ l, IsChannel (t l)) ∧ (∀ l, IsChannel (r l)) ∧
      ∀ x y, p x y = ∑ l, q l * ∑ μ, r l μ y * t l x μ

/-- Restriction preserves the original output alphabet and uses the input subtype. -/
def restrict {α : Type} {k : ℕ} (p : α → Fin k → ℝ) (i : Finset α) :
    i → Fin k → ℝ := fun x => p x.val

private def outputSets (k d : ℕ) :=
  {s : Finset (Fin k) // s ∈ Finset.powersetCard d Finset.univ}

private def feasible {α : Type} {k d : ℕ} (p : α → Fin k → ℝ) (x : α) :
    Set (outputSets k d → ℝ) :=
  {q | (∀ s, 0 ≤ q s) ∧ (∑ s, q s = 1) ∧
    ∃ a : outputSets k d → Fin k → ℝ,
      (∀ s y, 0 ≤ a s y) ∧ (∀ s y, y ∉ s.val → a s y = 0) ∧
      (∀ s, ∑ y, a s y = q s) ∧ (∀ y, ∑ s, a s y = p x y)}

private lemma channel_decomposition {α β : Type} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : IsChannel p) :
    (∀ f : α → β, 0 ≤ ∏ x, p x (f x)) ∧
    (∑ f : α → β, ∏ x, p x (f x)) = 1 ∧
    ∀ x y, (∑ f : α → β, (∏ z, p z (f z)) * if f x = y then 1 else 0) = p x y := by
  sorry

private lemma simulable_common {α : Type} [Fintype α] {k d : ℕ}
    (hd : 1 ≤ d) (hk : d < k) (p : α → Fin k → ℝ) (h : IsSimulable d p) :
    ∃ q, ∀ x, q ∈ feasible (d := d) p x := by
  sorry

private lemma common_simulable {α : Type} [Fintype α] [Nonempty α] {k d : ℕ}
    (hd : 1 ≤ d) (hk : d < k) (p : α → Fin k → ℝ)
    (h : ∃ q, ∀ x, q ∈ feasible (d := d) p x) : IsSimulable d p := by
  sorry

private lemma empty_inputs_simulable {α : Type} [IsEmpty α] {k d : ℕ}
    (hd : 1 ≤ d) (hk : d < k) (p : α → Fin k → ℝ) : IsSimulable d p := by
  sorry

private lemma feasible_convex {α : Type} {k d : ℕ} (p : α → Fin k → ℝ) (x : α) :
    Convex ℝ (feasible (d := d) p x) := by
  sorry

private lemma output_sets_card {k d : ℕ} : Fintype.card (outputSets k d) = k.choose d := by
  sorry

private lemma helly_normalized {α β : Type} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → Set (β → ℝ)) (hc : ∀ x, Convex ℝ (f x))
    (hn : ∀ x q, q ∈ f x → ∑ s, q s = 1)
    (he : ¬ ∃ q, ∀ x, q ∈ f x) :
    ∃ i : Finset α, i.Nonempty ∧ i.card ≤ Fintype.card β ∧ ¬ ∃ q, ∀ x ∈ i, q ∈ f x := by
  sorry

/-- The Doolittle–Chitambar certificate-size conjecture for finite classical channels. -/
theorem result (m k d : ℕ) (hd : 1 ≤ d) (hk : d < k)
    (p : Fin m → Fin k → ℝ) (hp : IsChannel p) (h : ¬ IsSimulable d p) :
    ∃ i : Finset (Fin m), i.Nonempty ∧ i.card ≤ k.choose d ∧
      ¬ IsSimulable d (restrict p i) := by
  classical
  have hm : 0 < m := by
    by_contra hz
    have : m = 0 := by omega
    subst m
    exact h (empty_inputs_simulable hd hk p)
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hs : 0 < Fintype.card (outputSets k d) := by
    rw [output_sets_card]
    exact Nat.choose_pos (Nat.le_of_lt hk)
  haveI : Nonempty (outputSets k d) := Fintype.card_pos_iff.mp hs
  have he : ¬ ∃ q, ∀ x, q ∈ feasible (d := d) p x :=
    fun hq => h (common_simulable hd hk p hq)
  obtain ⟨i, hi, hcard, hempty⟩ := helly_normalized (feasible (d := d) p)
    (feasible_convex p) (fun _ _ hq => hq.2.1) he
  refine ⟨i, hi, by simpa only [output_sets_card] using hcard, ?_⟩
  intro hiSim
  obtain ⟨q, hq⟩ := simulable_common hd hk (restrict p i) hiSim
  apply hempty
  exact ⟨q, fun x hx => hq ⟨x, hx⟩⟩

end D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate
