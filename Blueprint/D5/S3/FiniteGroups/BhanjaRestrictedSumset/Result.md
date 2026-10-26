# Minima with at most two distinct summands

## Abstract

Odd restricted sumsets in elementary abelian 2-groups have smaller minima.

**Definition 1.1 (Ordinary h-fold sumset).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall h \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(G\right),\; \operatorname{hSumset}\left(h, A\right) = \operatorname{HSMul.hSMul}\left(h, A\right)$$

*Formalization.* `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.hSumset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

The ordinary sumset is the existing pointwise natural scalar action on finsets.

**Definition 1.2 (At most r different summands).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall h \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(G\right),\; \operatorname{restrictedSumset}\left(h, r, A\right) = \operatorname{Finset.image}\left(\lambda (f: \operatorname{Fin}\left(h\right) \to G) \mapsto (\sum_{i: \operatorname{Fin}\left(h\right)} f\left(i\right)), \operatorname{Finset.filter}\left(\lambda (f: \operatorname{Fin}\left(h\right) \to G) \mapsto (\operatorname{Finset.card}\left(\operatorname{Finset.image}\left(f, \operatorname{Finset.univ}\left(\right)\right)\right) \le r), \operatorname{Fintype.piFinset}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(h\right), A\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.restrictedSumset` (`✓ std3`).

*Citation.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

§4, “Further Remarks”, printed p. 11: “Another sumset that may come immediately to the reader’s mind is the sumset h(≤r) A, which contains those elements of the group G that are the sum of h elements of A with at most r distinct elements.” The superscript appears as (≤r) in the text extraction. The finite image counts different values, allowing repetitions and allowing fewer than r values. Functions are enumerated by Fintype.piFinset, filtered by that cardinality and mapped to their sums.

**Theorem 1.3 (Function characterization of restricted sums).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall h \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(G\right),\; \forall x \in G,\; (x \in \operatorname{restrictedSumset}\left(h, r, A\right)) \Leftrightarrow (\exists f \in \operatorname{Fin}\left(h\right) \to G,\; (\forall i \in \operatorname{Fin}\left(h\right),\; f\left(i\right) \in A) \land ((\operatorname{Finset.card}\left(\operatorname{Finset.image}\left(f, \operatorname{Finset.univ}\left(\right)\right)\right) \le r) \land (\sum_{i: \operatorname{Fin}\left(h\right)} f\left(i\right) = x)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.memR` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

Membership in the filtered finite function space gives precisely the membership and image-cardinality conditions. This characterization is used to prove the restricted identity.

**Theorem 1.4 (Twice every vector is zero).**

$$\forall m \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right),\; \operatorname{HSMul.hSMul}\left(2, a\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.doubleZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

ZModModule.char_nsmul_eq_zero gives the characteristic-two identity for this module over ZMod 2.

**Theorem 1.5 (Odd repetition recovers the vector).**

$$\forall m \in \mathbb{N},\; \forall h \in \mathbb{N},\; (\operatorname{Odd}\left(h\right)) \Rightarrow (\forall a \in \operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right),\; \operatorname{HSMul.hSMul}\left(h, a\right) = a)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.oddSmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

The scalar coefficient reduces modulo two. Odd coefficients have remainder one. Constant functions therefore recover every member of A.

**Theorem 1.6 (An odd sum of two possible values is one of them).**

$$\forall m \in \mathbb{N},\; \forall h \in \mathbb{N},\; (\operatorname{Odd}\left(h\right)) \Rightarrow (\forall f \in \operatorname{Fin}\left(h\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right)\right),\; \forall a \in \operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right),\; \forall b \in \operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right),\; (\forall i \in \operatorname{Fin}\left(h\right),\; (f\left(i\right) = a) \lor (f\left(i\right) = b)) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(h\right)} f\left(i\right) = a) \lor (\sum_{i: \operatorname{Fin}\left(h\right)} f\left(i\right) = b)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.pairSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

Partition the indices according to f i = a. The two multiplicities add to h, so exactly one is odd. Reducing both scalar coefficients modulo two gives one of a and b.

**Theorem 1.7 (The restricted odd sumset equals A).**

$$\forall m \in \mathbb{N},\; \forall h \in \mathbb{N},\; (\operatorname{Odd}\left(h\right)) \Rightarrow (\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right)\right),\; \operatorname{restrictedSumset}\left(h, 2, A\right) = A)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.restrictedOdd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

The nonempty image of a function of odd positive length has cardinality one or two. In the singleton case its sum is that value; in the pair case pairSum gives one of the values. Conversely a constant function realizes every member of A.

**Theorem 1.8 (More than half the group gives every pair sum).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] [\operatorname{Fintype}\left(G\right)] \forall A \in \operatorname{Finset}\left(G\right),\; (\operatorname{Fintype.card}\left(G\right) < 2 \cdot \operatorname{Finset.card}\left(A\right)) \Rightarrow (A + A = \operatorname{Finset.univ}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.largeDouble` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

For each g the image of A under a ↦ g−a has the same cardinality as A. Finset.inter_nonempty_of_card_lt_card_add_card gives an intersection with A, hence a representation of g as two members of A.

**Theorem 1.9 (Cardinality growth gives all longer sumsets).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] [\operatorname{Fintype}\left(G\right)] \forall h \in \mathbb{N},\; (2 \le h) \Rightarrow (\forall A \in \operatorname{Finset}\left(G\right),\; (\operatorname{Fintype.card}\left(G\right) < 2 \cdot \operatorname{Finset.card}\left(A\right)) \Rightarrow (\operatorname{hSumset}\left(h, A\right) = \operatorname{Finset.univ}\left(\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.largeIterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

The pair sumset is the whole group. For h≥2, Finset.card_nsmul_mono bounds its cardinality by that of h•A, while Finset.card_le_univ bounds the latter by the group order. Finset.eq_univ_of_card gives the equality.

**Theorem 1.10 (The elementary 2-group family).**

$$\forall m \in \mathbb{N},\; (2 \le m) \Rightarrow (\forall h \in \mathbb{N},\; (\operatorname{Odd}\left(h\right)) \Rightarrow ((3 \le h) \Rightarrow (\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right)\right),\; ((2)^{m - 1} < \operatorname{Finset.card}\left(A\right)) \Rightarrow ((\operatorname{Finset.card}\left(A\right) < (2)^{m}) \Rightarrow ((\operatorname{restrictedSumset}\left(h, 2, A\right) = A) \land (\operatorname{hSumset}\left(h, A\right) = \operatorname{Finset.univ}\left(\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.elementary_two_group_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

For m≥2 and a subset in the strict half-to-full range, restrictedOdd gives the restricted identity and largeIterated gives the ordinary identity. The upper endpoint is retained to describe the strict-gap range; the ordinary covering identity itself only needs the lower bound.

**Definition 1.11 (Minimum ordinary cardinality).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall k \in \mathbb{N},\; \forall h \in \mathbb{N},\; \operatorname{minSize}\left(G, k, h\right) = \operatorname{sInf}\left(\{n: \mathbb{N} | (\exists A \in \operatorname{Finset}\left(G\right),\; (\operatorname{Finset.card}\left(A\right) = k) \land (\operatorname{Finset.card}\left(\operatorname{hSumset}\left(h, A\right)\right) = n))\}\right)$$

*Formalization.* `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.minSize` (`✓ std3`).

*Citation.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

The natural-number infimum runs over cardinalities of ordinary sumsets for every k-element finset. When a k-element finset exists, the nonempty set of natural numbers has a least element.

**Definition 1.12 (Minimum restricted cardinality).**

$$\forall G \in Type*,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall k \in \mathbb{N},\; \forall h \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{minRestrictedSize}\left(G, k, h, r\right) = \operatorname{sInf}\left(\{n: \mathbb{N} | (\exists A \in \operatorname{Finset}\left(G\right),\; (\operatorname{Finset.card}\left(A\right) = k) \land (\operatorname{Finset.card}\left(\operatorname{restrictedSumset}\left(h, r, A\right)\right) = n))\}\right)$$

*Formalization.* `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.minRestrictedSize` (`✓ std3`).

*Citation.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

The same minimization is performed for the at-most-r-distinct sumset. Both minima optimize over all k-element subsets, not just a selected witness.

**Definition 1.13 (The equality asked in Question 1).**

$$claim = \left(\forall G \in Type,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall h \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall r \in \mathbb{N},\; (1 \le h) \Rightarrow ((2 \le r) \Rightarrow ((\exists A \in \operatorname{Finset}\left(G\right),\; \operatorname{Finset.card}\left(A\right) = k) \Rightarrow (\operatorname{minRestrictedSize}\left(G, k, h, r\right) = \operatorname{minSize}\left(G, k, h\right))))\right)$$

*Formalization.* `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.claim` (`✓ std3`).

*Citation.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

§4, “Further Remarks”, printed p. 11: “Question 1. Is it always the case that the minimum size of both the sumsets hA and h(≤r) A are the same in any abelian group G, where the minimum runs over the subsets of G of size (say) k?” The preceding sentence specifies r ≥ 2. The claim uses h ≥ 1 and an attainable cardinality k, quantifies over all abelian groups in Type, and compares the two natural-number minima. Allowing k=0 adds a true empty-set case; the refutation uses k=3.

**Theorem 1.14 (A constant cardinality determines the minimum).**

$$\forall G \in Type*,\; [\operatorname{DecidableEq}\left(G\right)] \forall k \in \mathbb{N},\; \forall v \in \mathbb{N},\; \forall F \in \operatorname{Finset}\left(G\right) \to \operatorname{Finset}\left(G\right),\; (\exists A \in \operatorname{Finset}\left(G\right),\; \operatorname{Finset.card}\left(A\right) = k) \Rightarrow ((\forall A \in \operatorname{Finset}\left(G\right),\; (\operatorname{Finset.card}\left(A\right) = k) \Rightarrow (\operatorname{Finset.card}\left(F\left(A\right)\right) = v)) \Rightarrow (\operatorname{sInf}\left(\{n: \mathbb{N} | (\exists A \in \operatorname{Finset}\left(G\right),\; (\operatorname{Finset.card}\left(A\right) = k) \land (\operatorname{Finset.card}\left(F\left(A\right)\right) = n))\}\right) = v))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.uniformMinimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

If every k-element finset has the same image cardinality v and one such finset exists, the set of cardinalities is the singleton {v}; its infimum is v. This is used for both minima.

**Theorem 1.15 (Exact minima throughout the family).**

$$\forall m \in \mathbb{N},\; (2 \le m) \Rightarrow (\forall h \in \mathbb{N},\; (\operatorname{Odd}\left(h\right)) \Rightarrow ((3 \le h) \Rightarrow (\forall k \in \mathbb{N},\; ((2)^{m - 1} < k) \Rightarrow ((k < (2)^{m}) \Rightarrow ((\operatorname{minRestrictedSize}\left(\operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right), k, h, 2\right) = k) \land (\operatorname{minSize}\left(\operatorname{Fin}\left(m\right) \to \operatorname{ZMod}\left(2\right), k, h\right) = (2)^{m}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.elementary_two_group_minima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

There exists a k-element subset since k<2^m. The two identities for every such subset make the respective cardinality sets {k} and {2^m}. Thus the minima are k and 2^m, with a strict inequality in the given range.

**Theorem 1.16 (Question 1 has a negative answer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhanja-2025-restricted-sumset-question` (refuted) by `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhanja-2025-restricted-sumset-question","declaration_gid":"D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jagannath Bhanja (2025). *Sumsets with a minimum number of distinct terms*. URL: <https://arxiv.org/abs/2307.03977v2>.

*Commentary.*

At m=2, h=3, k=3 and r=2, the two exact minima are 3 and 4. Their equality would imply 3=4. The general family establishes both minima before this specialization.

## References

- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.claim`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.doubleZero`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.elementary_two_group_gap`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.elementary_two_group_minima`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.hSumset`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.largeDouble`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.largeIterated`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.memR`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.minRestrictedSize`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.minSize`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.oddSmul`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.pairSum`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.restrictedOdd`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.restrictedSumset`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.result`
- Truth anchor: `D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.uniformMinimum`
