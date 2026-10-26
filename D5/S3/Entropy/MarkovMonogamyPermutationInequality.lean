/- GID: D5/S3/Entropy/MarkovMonogamyPermutationInequality
   generality: G
   mirror-B: D5/B/S3/Entropy/MarkovMonogamyPermutationInequality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every finite Markov chain satisfies the permutation monogamy inequality. -/

import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import Mathlib.GroupTheory.Perm.Fin

/-! Finite Markov laws, their four-point information rectangles, and permutation exchange. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.MarkovMonogamyPermutationInequality

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.StrongSubadditivity

/-- The matrix product of the successive transitions from position `s` to position `t`.
Only transitions with indices in the half-open interval `[s,t)` are read. -/
noncomputable def composedTransition {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s t : ℕ) (h : s ≤ t) : α s → α t → ℝ := by
  classical
  exact Nat.leRecOn (C := fun t => α s → α t → ℝ) h
    (fun {t} u a b => ∑ c, u a c * k t c b) (fun a b => if a = b then 1 else 0)

/-- The initial law pushed through the transitions preceding position `t`. -/
noncomputable def positionLaw {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ) (t : ℕ) (b : α t) : ℝ :=
  ∑ a, p a * composedTransition k 0 t (Nat.zero_le t) a b

/-- The joint mass at two ordered positions: the earlier law times the intervening channel. -/
noncomputable def pairLaw {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ)
    (s t : ℕ) (h : s ≤ t) (q : α s × α t) : ℝ :=
  positionLaw p k s q.1 * composedTransition k s t h q.1 q.2

/-- Positions are `Xₙ,…,X₁,Y₁,…,Yₙ`. The alphabet family outside the first `2*n`
positions is irrelevant; stochasticity is required only for transitions inside this chain.
For `n = 0` both sums are empty. -/
def claim : Prop :=
  ∀ (n : ℕ) (α : ℕ → Type) [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ),
    ((∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1) →
    (∀ t, t + 1 < 2 * n → (∀ a b, 0 ≤ k t a b) ∧ ∀ a, ∑ b, k t a b = 1) →
    ∀ f : Equiv.Perm (Fin n),
      (∑ i : Fin n, mutualInformation
        (pairLaw p k (n - 1 - i.val) (n + (f i).val) (by omega))) ≤
      ∑ i : Fin n, mutualInformation
        (pairLaw p k (n - 1 - i.val) (n + i.val) (by omega))

private theorem composed_self {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s : ℕ) (a b : α s) :
    composedTransition k s s (le_refl s) a b =
      @ite ℝ (a = b) (Classical.propDecidable _) 1 0 := by
  sorry

private theorem composed_step {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s t : ℕ) (h : s ≤ t)
    (a : α s) (b : α (t + 1)) :
    composedTransition k s (t + 1) (by omega) a b =
      ∑ c, composedTransition k s t h a c * k t c b := by
  sorry

private theorem composed_comp {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s u t : ℕ) (hsu : s ≤ u) (hut : u ≤ t)
    (a : α s) (b : α t) :
    composedTransition k s t (hsu.trans hut) a b =
      ∑ c, composedTransition k s u hsu a c * composedTransition k u t hut c b := by
  sorry

private theorem composed_stochastic {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (k : ∀ t, α t → α (t + 1) → ℝ) (s t : ℕ) (h : s ≤ t)
    (hk : ∀ u, s ≤ u → u < t →
      (∀ a b, 0 ≤ k u a b) ∧ ∀ a, ∑ b, k u a b = 1) :
    (∀ a b, 0 ≤ composedTransition k s t h a b) ∧
      ∀ a, ∑ b, composedTransition k s t h a b = 1 := by
  sorry

private theorem position_transport {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ)
    (s t : ℕ) (h : s ≤ t) (b : α t) :
    positionLaw p k t b = ∑ a, positionLaw p k s a * composedTransition k s t h a b := by
  sorry

private theorem position_is_law {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ) (t : ℕ)
    (hp : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1)
    (hk : ∀ u, u < t → (∀ a b, 0 ≤ k u a b) ∧ ∀ a, ∑ b, k u a b = 1) :
    (∀ a, 0 ≤ positionLaw p k t a) ∧ ∑ a, positionLaw p k t a = 1 := by
  sorry

private theorem four_point_rectangle {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (p : α → ℝ) (u : α → β → ℝ) (v : β → γ → ℝ) (w : γ → δ → ℝ)
    (hp : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1)
    (hu : (∀ a b, 0 ≤ u a b) ∧ ∀ a, ∑ b, u a b = 1)
    (hv : (∀ b c, 0 ≤ v b c) ∧ ∀ b, ∑ c, v b c = 1)
    (hw : (∀ c d, 0 ≤ w c d) ∧ ∀ c, ∑ d, w c d = 1) :
    mutualInformation (fun q : β × γ => (∑ a, p a * u a q.1) * v q.1 q.2) +
      mutualInformation (fun q : α × δ => p q.1 * ∑ b, u q.1 b * ∑ c, v b c * w c q.2) ≥
    mutualInformation (fun q : β × δ => (∑ a, p a * u a q.1) * ∑ c, v q.1 c * w c q.2) +
      mutualInformation (fun q : α × γ => p q.1 * ∑ b, u q.1 b * v b q.2) := by
  sorry

private theorem chain_rectangle {α : ℕ → Type*} [∀ t, Fintype (α t)]
    (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ)
    (hp : (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1)
    (a b c d : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hk : ∀ u, u < d → (∀ x y, 0 ≤ k u x y) ∧ ∀ x, ∑ y, k u x y = 1) :
    mutualInformation (pairLaw p k b c hbc) +
      mutualInformation (pairLaw p k a d (by omega)) ≥
    mutualInformation (pairLaw p k b d (by omega)) +
      mutualInformation (pairLaw p k a c (by omega)) := by
  sorry

private theorem monge_permutation (n : ℕ) (m : Fin n → Fin n → ℝ)
    (hm : ∀ i j a b, i < j → a < b → m i a + m j b ≥ m i b + m j a)
    (f : Equiv.Perm (Fin n)) : (∑ i, m i (f i)) ≤ ∑ i, m i i := by
  sorry

/-- The classical Markov monogamy inequalities hold for every size and every permutation. -/
theorem result : claim := by
  intro n α inst p k hp hk f
  apply monge_permutation n
    (fun i a => mutualInformation (pairLaw p k (n - 1 - i.val) (n + a.val) (by omega)))
    ?_ f
  intro i j a b hij hab
  exact chain_rectangle p k hp (n - 1 - j.val) (n - 1 - i.val)
    (n + a.val) (n + b.val) (by omega) (by omega) (by omega)
    (fun u hu => hk u (by have hb := b.isLt; omega))

end D5.S3.Entropy.MarkovMonogamyPermutationInequality
