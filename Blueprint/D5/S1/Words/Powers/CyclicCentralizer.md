# A Unique Generator for a Word Centralizer

## Abstract

Classify the full centralizer of a nonempty finite word by its unique nonempty generator.

**Theorem 1.1 (The full centralizer has exactly one nonempty word generator).**

$$\forall ell \in Universe,\; \forall A \in \operatorname{Type}\left(ell\right),\; \forall w \in \operatorname{List}\left(A\right),\; (w \ne \operatorname{nil}\left(\right)) \Rightarrow (\exists r \in \operatorname{List}\left(A\right),\; ((r \ne \operatorname{nil}\left(\right)) \land (\forall v \in \operatorname{List}\left(A\right),\; (\operatorname{append}\left(w, v\right) = \operatorname{append}\left(v, w\right)) \Leftrightarrow (\exists n \in \mathbb{N},\; v = \operatorname{wordPower}\left(n, r\right)))) \land (\forall s \in \operatorname{List}\left(A\right),\; ((s \ne \operatorname{nil}\left(\right)) \land (\forall v \in \operatorname{List}\left(A\right),\; (\operatorname{append}\left(w, v\right) = \operatorname{append}\left(v, w\right)) \Leftrightarrow (\exists n \in \mathbb{N},\; v = \operatorname{wordPower}\left(n, s\right)))) \Rightarrow (s = r)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/CyclicCentralizer.exists_unique_centralizer_root` (`✓ std3`). ∎

*Citation.* M. Lothaire (1983). *Combinatorics on Words*. URL: <https://www-igm.univ-eiffel.fr/~berstel/Lothaire/lo1.ps>.

*Commentary.*

For every universe level ell, every alphabet type A in Type ell, and every nonempty finite word w over A, there is exactly one nonempty word r such that every finite word v commutes with w exactly when v is a natural power of r. The displayed formula expands unique existence into existence and equality of every competing generator. It therefore specifies the literal list r, not just its length or a pairwise common power.

The operation append is list concatenation, nil is the empty list, and wordPower(n,r) is the concatenation of n copies of r. The quantifier on v includes nil, and n=0 supplies that commuting word. There is no Finite, Fintype, ordering, inhabitedness, or DecidableEq premise on A. For an empty alphabet there is no nonempty input w; infinite alphabets are included without a change of statement.

Choose a positive-power root r of w with least positive length. The public Fine-Wilf supplier CommonPositivePowers.append_comm_of_flatten_replicate_eq shows that any two positive-power roots of this same w commute. The public theorem CommutingWords.commute_iff_common_power then writes r and any such root s as powers of a common t. Nested list replication makes t a positive-power root of w. Minimality and the nonzero length of t force the exponent expressing r to be one. Hence every such s is a power of r. Applying the pairwise theorem to w and an arbitrary commuting v now puts all commuting words in this single generated monoid.

If another nonempty word s generates the same centralizer, r and s are powers of each other. Their positive lengths force both exponents to be one, giving s=r. Lothaire's hosted Chapter 1, Section 1.3, Proposition 1.3.2, p. 7, gives the centralizer statement; the nonempty uniqueness sentence of Proposition 1.3.1 gives the primitive-root interpretation. These locators use the hosted chapter version, not unchecked pagination in another edition.

The separate CommonPositivePowers module contains four private period and reassembly helpers and the public theorem append_comm_of_flatten_replicate_eq, an Apache 2.0 transplant from Sebastien Gouezel's IETFree/ListPeriodicity.lean at immutable revision 48a23a630f39ae7c439b9efcbd03e729c18406fd. Both positive-exponent hypotheses and the original proof mechanism are retained. The source notice, complete license, immutable locator, and retirement condition against this repository's pinned Mathlib accompany the source and the literature note. No prefix-comparison or group code is included.

## References

- Truth anchor: `D5/S1/Words/Powers/CyclicCentralizer.exists_unique_centralizer_root`
- Dependency: [D5/S1/Words/Powers/CommonPositivePowers](CommonPositivePowers.md)
- Dependency: [D5/S1/Words/Powers/CommutingWords](CommutingWords.md)
