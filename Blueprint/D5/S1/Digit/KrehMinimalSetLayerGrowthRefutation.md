# Kreh's Minimal-Set Layer-Growth Conjecture

## Abstract

An infinite decimal-subsequence set has minimal-layer sizes 1, 2, and then 1 forever.

**Definition 1.1 (The decimal-string subsequence order).**

$$\forall a \in \mathbb{N}, b \in \mathbb{N},\; (\operatorname{digitSubseq}\left(a, b\right)) \Leftrightarrow (\operatorname{Sublist}\left(\operatorname{reverse}\left(\operatorname{digits}\left(10, a\right)\right), \operatorname{reverse}\left(\operatorname{digits}\left(10, b\right)\right)\right))$$

*Formalization.* `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.digitSubseq` (`✓ std3`).

*Citation.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

The decimal digit lists are reversed into printed order. Thus digitSubseq(a,b) is Kreh's decimal-subsequence relation: the printed decimal string of a is obtained from that of b by deleting zero or more digits.

**Definition 1.2 (Minimal elements of a set).**

$$\forall M \subseteq \mathbb{N}, \operatorname{minimal}\left(M\right) = \{a \in \mathbb{N} \mid (a \in M) \land (\forall b \in \mathbb{N},\; (b \in M) \Rightarrow ((\operatorname{digitSubseq}\left(b, a\right)) \Rightarrow (b = a)))\}$$

*Formalization.* `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.minimal` (`✓ std3`).

*Citation.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

An element a is retained precisely when it lies in M and every element of M whose decimal string is a subsequence of a equals a itself.

**Definition 1.3 (Successive removal of minimal elements).**

$$\forall M \subseteq \mathbb{N}, (\operatorname{peel}\left(M, 0\right) = M) \land (\forall k \in \mathbb{N},\; \operatorname{peel}\left(M, k + 1\right) = \operatorname{peel}\left(M, k\right) \setminus \operatorname{minimal}\left(\operatorname{peel}\left(M, k\right)\right))$$

*Formalization.* `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.peel` (`✓ std3`).

*Citation.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

The zeroth layer is M. Each successor layer removes exactly the minimal elements of the preceding layer.

**Definition 1.4 (The size of a minimal layer).**

$$\forall M \subseteq \mathbb{N}, \forall k \in \mathbb{N},\; \operatorname{eta}\left(M, k\right) = \operatorname{ncard}\left(\operatorname{minimal}\left(\operatorname{peel}\left(M, k\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.eta` (`✓ std3`).

*Citation.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

The value eta(M,k) is the finite-cardinality operator ncard applied to the minimal elements after k peelings. For an infinite set, ncard equals zero; the counterexample does not rely on that convention, because its layers are proved to be singletons or a pair.

**Definition 1.5 (The asserted divergence of minimal-layer sizes).**

$$(claim) \Leftrightarrow ((\forall M \subseteq \mathbb{N}, (\forall n \in \mathbb{N},\; (n \in M) \Rightarrow (0 < n)) \Rightarrow ((\operatorname{Infinite}\left(M\right)) \Rightarrow ((\operatorname{eta}\left(M, 0\right) < \operatorname{eta}\left(M, 1\right)) \Rightarrow (\forall B \in \mathbb{N},\; \exists N \in \mathbb{N},\; \forall k \in \mathbb{N},\; (N \le k) \Rightarrow (B \le \operatorname{eta}\left(M, k\right)))))))$$

*Formalization.* `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.claim` (`✓ std3`).

*Citation.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

The positivity premise expresses Kreh's convention that N contains the positive integers. For every infinite M with eta(M,0) below eta(M,1), the conclusion says that every natural bound eventually holds for all later layer sizes.

**Theorem 1.6 (The divergence claim is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kreh-2015-minimal-sets-conjecture-18` (refuted) by `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kreh-2015-minimal-sets-conjecture-18","declaration_gid":"D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Martin Kreh (2015). *Minimal Sets, Journal of Integer Sequences 18 (2015), Article 15.5.3*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kreh/kreh2.pdf>.

*Commentary.*

For M* = {1, 10, 11} union {110*10^j : j is natural}, the first minimal set is {1}, the next is {10, 11}, and the remaining set after k+2 peelings is the tail beginning at 110*10^k. Its minimal set is the first element of that tail, so the layer sizes are 1, 2, 1, 1, and then 1 forever. The countability sentence of Conjecture 18 is not asserted here.

## References

- Truth anchor: `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.claim`
- Truth anchor: `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.digitSubseq`
- Truth anchor: `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.eta`
- Truth anchor: `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.minimal`
- Truth anchor: `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.peel`
- Truth anchor: `D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.result`
