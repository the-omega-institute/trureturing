# First Mass Crossings in a Biased Binary Tree

## Abstract

First threshold crossings partition the biased binary boundary with exact total mass.

Let a and b be real letter probabilities with 0 < b <= a < 1 and a + b = 1. The alphabet is Bool: false has mass a and true has mass b. The function letterMass supplies these probabilities to wordMass, the product over the actual letters of a finite word. The empty word has mass one. Write m(w) for this product and parent(w) for the word obtained by deleting its last letter.

For 0 < t < 1, Crossing(a,b,t) consists exactly of the nonempty words w with m(w) <= t < m(parent(w)). Equality at the lower threshold is a stopping event. A ray is any function from the natural numbers to Bool; rayPrefix(r,n) is its first n letters. A word is a prefix of r precisely when w = rayPrefix(r,length(w)).

**Theorem 1.1 (A finite conservative frontier with reciprocal size bounds).**

$$\forall a, b, t \in \mathbb{R}, 0 < b \le a < 1 \land a + b = 1 \land 0 < t < 1 \Rightarrow \exists N \in \mathbb{N}, \exists A: \operatorname{Finset}\left(\operatorname{List}\left(Bool\right)\right), A = \operatorname{Crossing}\left(a, b, t\right) \land (\forall w \in A, \operatorname{length}\left(w\right) \le N) \land \operatorname{IsPrefixFree}\left(A\right) \land (\forall r: \mathbb{N} \to Bool, \exists! w, w \in A \land w = \operatorname{rayPrefix}\left(r, \operatorname{length}\left(w\right)\right)) \land \sum_{w \in A} \operatorname{m}\left(w\right) = 1 \land (\forall w \in A, b t < \operatorname{m}\left(w\right) \le t) \land \frac{1}{t} \le \operatorname{card}\left(A\right) < \frac{1}{b t}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/BiasedMassFrontier.biased_first_mass_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each letter has mass at most a, so m(w) <= a raised to length(w). Choose a common finite N for which a raised to N is less than t. Starting at the root, stop at a word of mass at most t; otherwise replace it by its two children. Every branch has stopped by N.

The two child subtrees are disjoint, and their masses add to their parent mass because a + b = 1. Induction on the finite remaining depth therefore preserves total mass exactly. Mass decreases under extension, so two first-crossing words cannot properly extend one another. Extending any word to depth N identifies the recursive leaves with the entire crossing set, and each infinite ray meets exactly one leaf.

At a crossing the parent mass is strictly greater than t and the last letter has mass at least b. Thus b times t is strictly less than each leaf mass, while every leaf mass is at most t. Summing these inequalities and using the conserved mass one gives the displayed cardinality bounds. The equal-probability case and thresholds equal to a word mass are included.

## References

- Truth anchor: `D5/S0/Computability/Coding/BiasedMassFrontier.biased_first_mass_frontier`
- Dependency: [D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality](DepthBudgetIidGreedyOptimality.md)
