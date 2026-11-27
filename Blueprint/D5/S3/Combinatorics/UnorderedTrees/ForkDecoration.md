# Unordered fork decorations

## Abstract

Normalized fork decorations correspond bijectively to the actual qualifying rooted-tree classes.

**Definition 1.1 (Normalized leaf offsets).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right), \left(\operatorname{Counts}\left(b, c\right) = \{\langle spine, short, long\rangle: \left(\operatorname{Fin}\left(b+c+1\right) \to \mathbb{N}\right) \times \mathbb{N} \times \mathbb{N} \mid c = 0 \Rightarrow short \le long\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Counts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spine multiplicities are unrestricted naturals. Each tip has one mandatory leaf beyond its offset, and equal arms require the short offset to be at most the long offset.

**Definition 1.2 (Data over both fork parameters).**

$$\operatorname{Data}\left(\right) = \Sigma b: \mathbb{N}, \Sigma c: \mathbb{N}, \operatorname{Counts}\left(b, c\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Data` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum includes the fork parameters and their corresponding multiplicity data.

**Definition 1.3 (Total size of the inflated fork).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) \left(r: \operatorname{Counts}\left(b, c\right)\right), \left(\operatorname{weight}\left(\langle b, c, r\rangle\right) = b+c+5+\sum_{i \in \operatorname{Fin}\left(b+c+1\right)} r.{spine}\left(i\right)+r.{short}+r.{long}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant term in the size accounts for the two tips, two mandatory tip leaves and the extra spine vertex.

**Definition 1.4 (Decorations of prescribed size).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{Weighted}\left(n\right) = \{d: \operatorname{Data}\left(\right) \mid \operatorname{weight}\left(d\right) = n\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Weighted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype consists of the decorations with total size n.

**Definition 1.5 (Actual qualifying tree classes).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{Qualifying}\left(n\right) = \{T: \operatorname{TreeClass}\left(n\right) \mid \operatorname{classHeight}\left(T\right) = \operatorname{classInternalCount}\left(T\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Qualifying` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype uses the quotient of actual parent data on Fin n and tests equality of the two class observables.

**Definition 1.6 (Leaf counts on the spine and tips).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) \left(r: \operatorname{Counts}\left(b, c\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(b+c+1\right)\right), \left(\begin{aligned}&r.{leaves}\left(\operatorname{inl}\left(i\right)\right) = r.{spine}\left(i\right)\\&r.{leaves}\left(\operatorname{inr}\left(false\right)\right) = r.{short}+1\\&r.{leaves}\left(\operatorname{inr}\left(true\right)\right) = r.{long}+1\end{aligned}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.leaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two tips use their offsets plus one. On every spine vertex the multiplicity is the corresponding spine coordinate.

**Definition 1.7 (A bijection at each total size).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{classification}\left(n\right): \operatorname{Weighted}\left(n\right) \equiv \operatorname{Qualifying}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.classification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inflation followed by labelling the complete carrier gives the forward map. Pruning recovers the canonical fork and reads the leaf multiplicities. Fork depth and maximum depth determine b and c. The spine is fixed by automorphisms, and sorting removes the tip-swap ambiguity at c=0, including equal tip counts.

**Theorem 1.8 (The decoration count equals the actual tree count).**

$$\forall n \in \mathbb{N},\; \left(Nat.{card}\left(\operatorname{Weighted}\left(n\right)\right) = \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.card_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cardinality is preserved by the size-matched classification.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Counts`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Data`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Qualifying`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.Weighted`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.card_weighted`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.classification`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.leaves`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.weight`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/LeafDecoration](LeafDecoration.md)
