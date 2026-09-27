# Weighted Identification of Sibling Residue Leaves

## Abstract

The least positive-weighted cost of identifying sibling residue leaves is attained by scanning in decreasing mass order and inferring the last leaf.

Fix a prime p and a natural number d. Let X be ZMod of p to the power d plus one. The actual response h(c,a) is the maximum index i from zero through d plus one for which the canonical natural representatives of a and c agree modulo p to the power i. The response q(c,a) is the Boolean equality test. Candidates S share one residue modulo p to the power d, and m assigns a strictly positive rational mass to each candidate. No normalization of these masses is required.

P is PassiveProtocol X with natural-number responses. R(T,a) means runPassiveProtocol h T a. I(T,S) means that equal R transcripts for two members of S imply equal targets. C(T,a) is the list of centers in R(T,a), and L(T,a) is its length. For an enumeration u from Fin k onto S, E(u,a) is the center list of the equality scan of List.ofFn of u, executed at a. Elements of S in these formulas are coerced to X. Set V contains exactly the rational costs of actual identifying protocols, as defined below.

**Theorem 1.1 (Schedule attainment and the actual weighted minimum).**

$$\begin{aligned}\forall p, d: \mathbb{N}, \operatorname{Prime}\left(p\right) \Rightarrow\\X = \operatorname{ZMod}\left(p^{d+1}\right), \forall S: \operatorname{Finset}\left(X\right),\\(\forall a \in S, \forall b \in S, \operatorname{ModEq}\left(p^{d}, \operatorname{val}\left(a\right), \operatorname{val}\left(b\right)\right)) \Rightarrow\\\forall m: X \to \mathbb{Q}, (\forall a \in S, 0 < \operatorname{m}\left(a\right)) \Rightarrow\\k = \operatorname{card}\left(S\right), \forall o: \operatorname{Equiv}\left(\operatorname{Fin}\left(k\right), S\right), \operatorname{Antitone}\left((i \mapsto \operatorname{m}\left(\operatorname{o}\left(i\right)\right))\right) \Rightarrow\\V = \{\sum_{a:S} \operatorname{m}\left(a\right) \operatorname{L}\left(T, a\right) \mid T: P, \operatorname{I}\left(T, S\right)\},\\(\forall u: \operatorname{Equiv}\left(\operatorname{Fin}\left(k\right), S\right), \exists T: P, \operatorname{I}\left(T, S\right) \land\\(\forall i: \operatorname{Fin}\left(k\right), \operatorname{L}\left(T, \operatorname{u}\left(i\right)\right) = \operatorname{min}\left(\operatorname{val}\left(i\right)+1, k-1\right)) \land\\(\forall a \in S, \operatorname{C}\left(T, a\right) = \operatorname{E}\left(u, a\right))) \land\\\operatorname{IsLeast}\left(V, \sum_{i:\operatorname{Fin}\left(k\right)} \operatorname{m}\left(\operatorname{o}\left(i\right)\right) \operatorname{min}\left(\operatorname{val}\left(i\right)+1, k-1\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/ResidueLeafOptimality.leaf_sibling_weighted_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A full-depth answer detects the queried leaf. All other sibling candidates give the same answer at a fixed center, including a center outside the candidate set. Relabeling continuation branches therefore converts actual and equality protocols in both directions while preserving every queried center and each target's count. Identification is retained.

The equality scan attains the capped position count. Conversely, the equality-query normal form supplies a schedule no slower at any target than a given identifying tree. Multiplying by positive masses preserves that lower bound, and the rearrangement inequality minimizes the schedule cost by pairing decreasing masses with increasing coefficients. This proves both membership in V and its lower-bound property.

For one candidate the coefficient is zero. For k at least two the coefficients are one through k minus two, followed by k minus one twice. Thus the last pair may exchange places without changing cost; earlier unequal coefficients favor the larger mass. A sorted enumeration begins with a maximum mass candidate. With two leaves every enumeration costs one query at either target. The last survivor is inferred without an extra query.

## References

- Truth anchor: `D5/S3/Observer/Budget/ResidueLeafOptimality.leaf_sibling_weighted_minimum`
- Dependency: [D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm](EqualityQueryScheduleNormalForm.md)
