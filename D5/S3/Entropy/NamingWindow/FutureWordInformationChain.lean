/- GID: D5/S3/Entropy/NamingWindow/FutureWordInformationChain
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/FutureWordInformationChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Model a length n+1 future word as recursively nested prefix-output pairs and expand its Shannon entropy into the first-readout entropy plus all prefix-conditional entropies. -/

import D5.S3.Entropy.ConditionalEntropy

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'future_word_information_chain' D5 Golden/Frozen/accepted` returned no hit.
   * Repository searches for future-word, iterated-entropy, prefix-conditional, chain-rule, and
     telescoping names found only the two-variable `entropy_chain_rule` and the distinct
     deterministic normalized-law result `deterministic_trajectory_entropy_telescoping`.
   * The five existing `Entropy/NamingWindow` digests concern green-class window entropy,
     divergence, equality, Hellinger distance, and total variation; none covers an n-fold chain.
   * The only repository `marginal_nonneg` theorem is private in `StrongSubadditivity`, so it is not
     reusable. The public nonnegativity lemmas below fill that downstream-facing gap.
   * Pinned mathlib contains `Fin.snocEquiv`, but no finite real-valued n-fold Shannon chain rule.
     Recursive prefix-output pairs avoid transport while applying `entropy_chain_rule` directly at
     every successor step. No entropy or conditional-entropy definition is duplicated here.
   * The cases `n = 0`, empty or singleton `O`, and `p = 0` require no extra hypothesis; neither
     normalization nor `Nonempty O` is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.NamingWindow.FutureWordInformationChain

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy

open scoped BigOperators

universe u

/-- A future word of length `n + 1`, recursively split as its prefix and final readout. -/
def FutureWord (O : Type u) : ℕ → Type u
  | 0 => O
  | n + 1 => FutureWord O n × O

/-- Finite readout alphabets give finite future-word alphabets at every length. -/
instance futureWordFintype {O : Type u} [Fintype O] : ∀ n, Fintype (FutureWord O n)
  | 0 => inferInstanceAs (Fintype O)
  | n + 1 =>
      letI : Fintype (FutureWord O n) := futureWordFintype n
      inferInstanceAs (Fintype (FutureWord O n × O))

/-- The law of the first readout, obtained by marginalizing every later readout. -/
noncomputable def firstReadoutMarginal {O : Type u} [Fintype O] :
    {n : ℕ} → (FutureWord O n → ℝ) → O → ℝ
  | 0, p => p
  | _ + 1, p => firstReadoutMarginal (marginal p)

/-- The conditional entropy of readout `j + 1` given the full prefix through readout `j`. -/
noncomputable def prefixConditionalEntropy {O : Type u} [Fintype O] :
    {n : ℕ} → (FutureWord O n → ℝ) → ℕ → ℝ
  | 0, _, _ => 0
  | n + 1, p, j =>
      if j = n then conditionalEntropy p else prefixConditionalEntropy (marginal p) j

/-- Marginalizing a nonnegative finite joint mass function preserves nonnegativity. -/
theorem marginal_nonnegative {ι κ : Type*} [Fintype κ] (p : ι × κ → ℝ)
    (hp : ∀ x, 0 ≤ p x) : ∀ i, 0 ≤ marginal p i := by
  classical
  intro i
  rw [marginal]
  exact Finset.sum_nonneg fun j _ => hp (i, j)

/-- Conditioning a nonnegative finite joint mass function preserves nonnegativity. -/
theorem conditional_nonnegative {ι κ : Type*} [Fintype κ] (p : ι × κ → ℝ)
    (hp : ∀ x, 0 ≤ p x) : ∀ i j, 0 ≤ conditional p i j := by
  intro i j
  exact div_nonneg (hp (i, j)) (marginal_nonnegative p hp i)

/-- Every recursively marginalized first-readout law remains nonnegative. -/
theorem firstReadoutMarginal_nonnegative {O : Type u} [Fintype O] {n : ℕ}
    (p : FutureWord O n → ℝ) (hp : ∀ w, 0 ≤ p w) :
    ∀ o, 0 ≤ firstReadoutMarginal p o := by
  induction n with
  | zero => simpa [FutureWord, firstReadoutMarginal] using hp
  | succ n ih =>
      simpa [firstReadoutMarginal] using
        ih (marginal p) (marginal_nonnegative p hp)

/-- Below the last index, successor-word conditional entropy is inherited from its prefix law. -/
theorem prefixConditionalEntropy_succ_of_lt {O : Type u} [Fintype O] {n j : ℕ}
    (p : FutureWord O (n + 1) → ℝ) (hj : j < n) :
    prefixConditionalEntropy p j = prefixConditionalEntropy (marginal p) j := by
  simp [prefixConditionalEntropy, Nat.ne_of_lt hj]

/-- The last conditional-entropy term of a successor word is its outer joint conditional entropy. -/
theorem prefixConditionalEntropy_succ_last {O : Type u} [Fintype O] {n : ℕ}
    (p : FutureWord O (n + 1) → ℝ) :
    prefixConditionalEntropy p n = conditionalEntropy p := by
  simp [prefixConditionalEntropy]

/-- Extending a word appends its last prefix-conditional entropy to the preceding sum. -/
theorem prefixConditionalEntropy_sum_succ {O : Type u} [Fintype O] {n : ℕ}
    (p : FutureWord O (n + 1) → ℝ) :
    (∑ j ∈ Finset.range (n + 1), prefixConditionalEntropy p j) =
      (∑ j ∈ Finset.range n, prefixConditionalEntropy (marginal p) j) +
        conditionalEntropy p := by
  rw [Finset.sum_range_succ, prefixConditionalEntropy_succ_last]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact prefixConditionalEntropy_succ_of_lt p (Finset.mem_range.mp hj)

/-- The entropy of a length `n + 1` future word is the first-readout entropy plus the sum of the
conditional entropies of every later readout given its entire preceding prefix. -/
theorem future_word_information_chain {O : Type u} [Fintype O] (n : ℕ)
    (p : FutureWord O n → ℝ) (hp : ∀ w, 0 ≤ p w) :
    shannonEntropy p =
      shannonEntropy (firstReadoutMarginal p) +
        ∑ j ∈ Finset.range n, prefixConditionalEntropy p j := by
  induction n with
  | zero =>
      simp [FutureWord, firstReadoutMarginal]
      rfl
  | succ n ih =>
      have hmarginal : ∀ w, 0 ≤ marginal p w := marginal_nonnegative p hp
      have hprefix := ih (marginal p) hmarginal
      calc
        shannonEntropy p =
            shannonEntropy (marginal p) + conditionalEntropy p :=
          entropy_chain_rule p hp
        _ = (shannonEntropy (firstReadoutMarginal (marginal p)) +
              ∑ j ∈ Finset.range n, prefixConditionalEntropy (marginal p) j) +
                conditionalEntropy p := by rw [hprefix]
        _ = shannonEntropy (firstReadoutMarginal p) +
              ∑ j ∈ Finset.range (n + 1), prefixConditionalEntropy p j := by
          rw [prefixConditionalEntropy_sum_succ]
          simp only [firstReadoutMarginal]
          ring

example :
    shannonEntropy (fun _ : FutureWord Bool 2 => (0 : ℝ)) =
      shannonEntropy (firstReadoutMarginal (fun _ : FutureWord Bool 2 => (0 : ℝ))) +
        ∑ j ∈ Finset.range 2,
          prefixConditionalEntropy (fun _ : FutureWord Bool 2 => (0 : ℝ)) j := by
  exact future_word_information_chain 2 (fun _ : FutureWord Bool 2 => (0 : ℝ))
    (fun _ => le_rfl)

#print axioms future_word_information_chain

end D5.S3.Entropy.NamingWindow.FutureWordInformationChain
