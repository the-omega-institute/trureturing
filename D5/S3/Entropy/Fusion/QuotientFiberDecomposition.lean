/- GID: D5/S3/Entropy/Fusion/QuotientFiberDecomposition
   generality: G
   mirror-B: D5/B/S3/Entropy/Fusion/QuotientFiberDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite source law splits into quotient entropy and weighted fiber entropy. -/

/- Library-search audit trail (2026-08-22):
   * Exact repository hits `pushforward`, `conditional`, `conditionalEntropy`, and
     `entropy_chain_rule` construct the quotient law, normalized graph-law fibers, and both
     Shannon decompositions. All four are imported and directly applied below.
   * Exact repository hit `pushforward_entropy_eq_iff_injective_on_support` identifies the
     graph-law entropy with the source entropy; it is directly applied to the injective map
     `x |-> (q x, x)`.
   * Pinned Mathlib searches for `conditionalEntropy`, `conditional_entropy`, entropy chain-rule
     names in both orders, `shannonEntropy`, and `finiteEntropy` found scalar
     `Real.negMulLog`/binary entropy but no real-valued finite Shannon chain rule.
   * Loogle query `"entropy"` returned the scalar binary and q-ary entropy families but no exact
     finite decomposition. LeanSearch query `finite Shannon entropy chain rule decomposition into
     entropy of a function and conditional entropy` likewise returned only scalar binary-entropy
     results. No stronger library theorem was found.
-/

import D5.S3.Entropy.Forgetting.DeterministicEntropyEquality

namespace D5.S3.Entropy.Fusion.QuotientFiberDecomposition

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
open D5.S3.Entropy.MaxEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The entropy of a finite normalized source law is the entropy of its deterministic quotient
plus the quotient-mass-weighted entropy of the normalized graph-law fibers. The second conjunct
records the same source decomposition through the canonical conditional-entropy aggregate. -/
theorem quotient_fiber_entropy_decomposition
    {X B : Type*} [Fintype X] [Fintype B]
    (mass : X -> Real) (q : X -> B)
    (mass_nonnegative : forall x, 0 <= mass x)
    (mass_total : ∑ x, mass x = 1) :
    shannonEntropy mass =
        shannonEntropy (pushforward q mass) +
          ∑ b, pushforward q mass b *
            shannonEntropy
              (conditional (pushforward (fun x => (q x, x)) mass) b) /\
      shannonEntropy mass =
        shannonEntropy (pushforward q mass) +
          conditionalEntropy (pushforward (fun x => (q x, x)) mass) := by
  classical
  let graph : X -> B × X := fun x => (q x, x)
  let graphLaw : B × X -> Real := pushforward graph mass
  have graph_injective : Function.Injective graph := by
    intro x y hxy
    exact congrArg Prod.snd hxy
  have graph_entropy : shannonEntropy graphLaw = shannonEntropy mass := by
    exact (pushforward_entropy_eq_iff_injective_on_support
      mass graph ⟨mass_nonnegative, mass_total⟩).2 graph_injective.injOn
  have graph_nonnegative : forall z, 0 <= graphLaw z := by
    intro z
    simp only [graphLaw, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases hx : graph x = z <;> simp [hx, mass_nonnegative x]
  have graph_marginal : marginal graphLaw = pushforward q mass := by
    funext b
    simp only [marginal, graphLaw, graph, pushforward]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : q x = b <;> simp [hx]
  have chain := entropy_chain_rule graphLaw graph_nonnegative
  have expanded := chain
  rw [conditionalEntropy, graph_marginal, graph_entropy] at expanded
  rw [graph_entropy, graph_marginal] at chain
  exact ⟨by simpa only [graphLaw, graph] using expanded,
    by simpa only [graphLaw, graph] using chain⟩

/-- The uniform Boolean law witnesses that the source-law hypotheses are jointly inhabited. -/
example :
    (forall _x : Bool, 0 <= (1 / 2 : Real)) /\
      ∑ _x : Bool, (1 / 2 : Real) = 1 := by
  constructor
  · intro _x
    norm_num
  · norm_num [Fintype.sum_bool]

#print axioms quotient_fiber_entropy_decomposition

end D5.S3.Entropy.Fusion.QuotientFiberDecomposition
