# Commuting Words and Common Powers

## Abstract

Classify commuting finite words as natural powers of a common word.

**Theorem 1.1 (Full commutation classification).**

$$\forall ell \in Universe,\; \forall A \in \operatorname{Type}\left(ell\right),\; \forall u \in \operatorname{List}\left(A\right),\; \forall v \in \operatorname{List}\left(A\right),\; (\operatorname{append}\left(u, v\right) = \operatorname{append}\left(v, u\right)) \Leftrightarrow (\exists w \in \operatorname{List}\left(A\right),\; \exists m \in \mathbb{N},\; \exists n \in \mathbb{N},\; (u = \operatorname{wordPower}\left(m, w\right)) \land (v = \operatorname{wordPower}\left(n, w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/CommutingWords.commute_iff_common_power` (`✓ std3`). ∎

*Citation.* Juhani Karhumaki (2004). *Combinatorics on Words: A New Challenging Topic*. URL: <https://tucs.fi/publications/attachment.php?fname=TR645.pdf>.

*Commentary.*

For every universe level ell, every alphabet type A in Type ell, and all finite words u and v over A, concatenation commutes exactly when both words are natural powers of one word w. The operation append is list concatenation, and wordPower(k,w) is the concatenation of k copies of w. The exponents m and n may be zero, and w may be empty. No finiteness or decidable equality assumption on A is required.

The forward implication uses induction on length(u)+length(v). If u is empty, take w=v with exponents 0 and 1; if v is empty, take w=u with exponents 1 and 0. Otherwise, splitting the equality of concatenations gives either v=append(u,r)=append(r,u), or the symmetric equations for u. The shorter pair therefore commutes and has smaller total length. Its common word also generates the original pair, by adding exponents. For the reverse implication, FreeMonoid.ofList identifies concatenation with multiplication and wordPower with natural monoid powers. Commute.pow_pow_self supplies commutation of these powers.

Section 3, Theorem 1(i)-(ii) of the cited report gives this classical equivalence and explicitly treats empty words. The source introduces finite alphabets; the statement here allows an arbitrary type. It asserts existence of a common word and exponents, without a primitive-root uniqueness or shortest-root conclusion.

## References

- Truth anchor: `D5/S1/Words/Powers/CommutingWords.commute_iff_common_power`
