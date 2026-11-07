# Centralizer Orbits in a Frobenius Action

## Abstract

A derangement's centralizer acts freely under the two-point fixed condition, so its order divides the finite action's degree.

**Theorem 1.1 (Nonidentity centralizer elements move every point).**

$$\forall u v, \forall G \in \operatorname{Type} u,\; \forall X \in \operatorname{Type} v,\; [\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, X\right)], (\forall g \in G,\; (g \ne 1) \Rightarrow (\forall x \in X,\; \forall y \in X,\; (\operatorname{SMul}.\operatorname{smul}\left(g, x\right) = x) \Rightarrow ((\operatorname{SMul}.\operatorname{smul}\left(g, y\right) = y) \Rightarrow (x = y)))) \Rightarrow (\forall d \in G,\; (\forall x \in X,\; \operatorname{SMul}.\operatorname{smul}\left(d, x\right) \ne x) \Rightarrow (\forall c \in \operatorname{Subgroup}.\operatorname{centralizer}\left((\{d\}: \operatorname{Set}\left(G\right))\right),\; (c \ne 1) \Rightarrow (\forall x \in X,\; \operatorname{SMul}.\operatorname{smul}\left(c, x\right) \ne x)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic.centralizer_smul_ne_self_of_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G act on X, with every nonidentity element fixing at most one point, and let d be a derangement: d moves every point of X. If a nonidentity element c of the subgroup Subgroup.centralizer {d} fixed x, its commutation with d would also make it fix d acting on x. The two-point fixed condition would identify x with d acting on x, contradicting the derangement premise. Thus the restricted centralizer action is free. G and X may be infinite and may lie in different universes.

**Theorem 1.2 (Centralizer order divides the degree).**

$$\forall u v, \forall G \in \operatorname{Type} u,\; \forall X \in \operatorname{Type} v,\; [\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, X\right)], [\operatorname{Finite}\left(G\right)], [\operatorname{Finite}\left(X\right)], (\forall g \in G,\; (g \ne 1) \Rightarrow (\forall x \in X,\; \forall y \in X,\; (\operatorname{SMul}.\operatorname{smul}\left(g, x\right) = x) \Rightarrow ((\operatorname{SMul}.\operatorname{smul}\left(g, y\right) = y) \Rightarrow (x = y)))) \Rightarrow (\forall d \in G,\; (\forall x \in X,\; \operatorname{SMul}.\operatorname{smul}\left(d, x\right) \ne x) \Rightarrow (\operatorname{Nat}.\operatorname{card}\left(\operatorname{Subgroup}.\operatorname{centralizer}\left((\{d\}: \operatorname{Set}\left(G\right))\right)\right) \mid \operatorname{Nat}.\operatorname{card}\left(X\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic.card_centralizer_dvd_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When G and X are finite, the first theorem makes every stabilizer of the restricted centralizer action trivial. The pinned Mathlib equivalence MulAction.selfEquivOrbitsQuotientProd identifies X with its centralizer-orbit quotient times the centralizer. Nat.card_congr and Nat.card_prod then give the displayed divisibility.

The empty type X is allowed: its degree is zero, and the divisibility still holds. Transitivity, faithfulness and nonemptiness are not assumed. These statements give the centralizer free-action argument and its orbit arithmetic; they assert neither the Frobenius kernel theorem nor a classification of Frobenius groups. The exposition records the repository derivation without a literature novelty claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic.card_centralizer_dvd_card`
- Truth anchor: `D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic.centralizer_smul_ne_self_of_ne_one`
