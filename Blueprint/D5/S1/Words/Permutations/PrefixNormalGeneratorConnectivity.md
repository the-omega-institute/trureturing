# Connectivity of prefix normal generators

## Abstract

Valid flip-to-zero generators are connected by finite adjacent-position exchanges.

The source is Adamson, Dudey, Fleischmann and Huch, arXiv:2508.19619v1. Its Conclusion asks whether any prefix normal generator can reach all others by swapping neighbouring entries. The result below answers exactly that v1 question in a zero-based model, for every natural n and hence every positive n. The later Springer chapter body is inaccessible and has not been compared with v1; its answer status remains ASSUMED-UNVERIFIED. This exposition asserts neither current literature priority nor a counted resolution.

A set S represents a binary word of fixed length n: position i has bit 1 exactly when i belongs to S, for 0<=i<n. The actual chain sets are subsets of range(n). The source coordinate is i+1, and a zero-based permutation entry a means flipping source position a+1. Adding one to every entry is a bijection with permutations of 1,...,n and preserves list positions, order of flips and adjacency. After t flips, source component t+1 is the characteristic word of range(n) minus take(t,l). All times 0<=t<=n are quantified; permutation length and distinctness give precisely n+1 states, starting at all ones and ending at all zeros.

**Definition 1.1 (Factor count).**

$$\forall ( S : \operatorname {Finset}\left(\mathbb {N}\right) ) , \forall ( s : \mathbb {N} ) , \forall ( ell : \mathbb {N} ) , \operatorname {count}\left(S, s, ell\right) = \operatorname {card}\left(\operatorname {inter}\left(S, \operatorname {Ico}\left(s, s + ell\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.count` (`✓ std3`).

*Citation.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

inter denotes finite-set intersection. Ico(s,s+ell) is the half-open interval [s,s+ell); card counts its occupied positions. Thus count agrees with the number of ones in a contiguous binary factor.

**Definition 1.2 (Prefix normality).**

$$\forall ( n : \mathbb {N} ) , \forall ( S : \operatorname {Finset}\left(\mathbb {N}\right) ) , \operatorname {PN}\left(n, S\right) \iff \forall ( s : \mathbb {N} ) , \forall ( ell : \mathbb {N} ) , s + ell \le n \implies \operatorname {count}\left(S, s, ell\right) \le \operatorname {count}\left(S, 0, ell\right)$$

*Formalization.* `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.PN` (`✓ std3`).

*Citation.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

Every factor ending at or before n is compared with the prefix of the same length. Zero lengths, zero counts, empty words and factors ending exactly at n are included. The predicate itself is also defined on unrestricted finite sets; only the permutation-chain uses assert the binary word of length n.

**Theorem 1.3 (Deleting one occupied position).**

$$\forall ( S : \operatorname {Finset}\left(\mathbb {N}\right) ) , \forall ( s : \mathbb {N} ) , \forall ( ell : \mathbb {N} ) , \forall ( a : \mathbb {N} ) , \operatorname {count}\left(\operatorname {erase}\left(S, a\right), s, ell\right) = \operatorname {ite}\left(a \in S \land s \le a \land a < s + ell, \operatorname {count}\left(S, s, ell\right) - 1, \operatorname {count}\left(S, s, ell\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.count_erase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

Subtraction is natural subtraction. This finite-set cardinality identity is consumed by erase_later_preserves and carries no separate research claim.

**Theorem 1.4 (Deletion farther to the right).**

$$\forall ( n : \mathbb {N} ) , \forall ( S : \operatorname {Finset}\left(\mathbb {N}\right) ) , \forall ( a : \mathbb {N} ) , \forall ( b : \mathbb {N} ) , a < b \implies a \in S \implies b \in S \implies \operatorname {PN}\left(n, S\right) \implies \operatorname {PN}\left(n, \operatorname {erase}\left(S, a\right)\right) \implies \operatorname {PN}\left(n, \operatorname {erase}\left(S, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.erase_later_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

For each factor, split according to whether b is in its equal-length prefix and in the factor. If both contain b, both counts lose one. If only the prefix contains b, interval geometry excludes a from the factor and the comparison comes from S with a erased. If the prefix excludes b, use monotonicity of deletion. The checked local fact is consumed by the ascent exchange.

**Definition 1.5 (Suffix form of chain validity).**

$$\forall ( n : \mathbb {N} ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {Generator}\left(n, l\right) \iff \operatorname {Perm}\left(l, \operatorname {range}\left(n\right)\right) \land \forall ( t : \mathbb {N} ) , t \le n \implies \operatorname {PN}\left(n, \operatorname {toFinset}\left(\operatorname {drop}\left(t, l\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.Generator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

The suffix lists the positions not yet flipped. This proof-facing predicate is equivalent to the direct undeleted-set predicate below.

**Theorem 1.6 (Published Lemma 17).**

$$\forall ( n : \mathbb {N} ) , \forall ( p : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( s : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( a : \mathbb {N} ) , \forall ( b : \mathbb {N} ) , a < b \implies \operatorname {Generator}\left(n, \operatorname {append}\left(p, \operatorname {cons}\left(a, \operatorname {cons}\left(b, s\right)\right)\right)\right) \implies \operatorname {Generator}\left(n, \operatorname {append}\left(p, \operatorname {cons}\left(b, \operatorname {cons}\left(a, s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.generator_ascent_swap` (`✓ std3`). ∎

*Citation.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

For q=length(p), the old and new states agree for t<=q and t>=q+2. Only t=q+1 differs, and erase_later_preserves proves its prefix normality. The source component of this state is q+2, as in the recurrence and Figure 5; the q+1 component references in the Lemma 17 prose are not used as assumptions. This is a published supply statement with an independent Lean proof.

**Definition 1.7 (Valid adjacent-position exchange).**

$$\forall ( P : \operatorname {List}\left(\mathbb {N}\right) \to Prop ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( m : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {Edge}\left(P, l, m\right) \iff \operatorname {P}\left(l\right) \land \operatorname {P}\left(m\right) \land \exists ( p : \operatorname {List}\left(\mathbb {N}\right) ) , \exists ( s : \operatorname {List}\left(\mathbb {N}\right) ) , \exists ( a : \mathbb {N} ) , \exists ( b : \mathbb {N} ) , l = \operatorname {append}\left(p, \operatorname {cons}\left(a, \operatorname {cons}\left(b, s\right)\right)\right) \land m = \operatorname {append}\left(p, \operatorname {cons}\left(b, \operatorname {cons}\left(a, s\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

Both endpoints satisfy P. A common prefix and suffix show literal adjacency of the exchanged positions; a,b need not be consecutive values. For generators they are distinct by permutation validity.

**Theorem 1.8 (Consumed insertion path).**

$$\forall ( P : \operatorname {List}\left(\mathbb {N}\right) \to Prop ) , ( \forall ( p : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( s : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( a : \mathbb {N} ) , \forall ( b : \mathbb {N} ) , a < b \implies \operatorname {P}\left(\operatorname {append}\left(p, \operatorname {cons}\left(a, \operatorname {cons}\left(b, s\right)\right)\right)\right) \implies \operatorname {P}\left(\operatorname {append}\left(p, \operatorname {cons}\left(b, \operatorname {cons}\left(a, s\right)\right)\right)\right) ) \implies \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( p : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {P}\left(\operatorname {append}\left(p, l\right)\right) \implies \operatorname {ReflTransGen}\left(\operatorname {Edge}\left(P\right), \operatorname {append}\left(p, l\right), \operatorname {append}\left(p, \operatorname {insertionSortDescending}\left(l\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

insertionSortDescending(l) denotes List.insertionSort with relation b<=a. Contextual inductions over insertion and the list construct actual adjacent edges while preserving P at every intermediate vertex. Generic Mathlib sorting is applied directly for permutation and sortedness below; this helper supplies the valid intermediate path and is consumed only by full_event_list.

**Theorem 1.9 (Connectivity in suffix coordinates).**

$$\forall ( n : \mathbb {N} ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( m : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {Generator}\left(n, l\right) \implies \operatorname {Generator}\left(n, m\right) \implies \operatorname {ReflTransGen}\left(\operatorname {Edge}\left(\operatorname {Generator}\left(n\right)\right), l, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.full_event_list` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

Normalize each endpoint to descending order using generator_ascent_swap. List.perm_insertionSort, List.pairwise_insertionSort and List.Perm.eq_of_pairwise' identify the sorted endpoints directly. Edge symmetry reverses the second path; transitivity joins them. This theorem is consumed by result.

**Theorem 1.10 (The actual binary-state correspondence).**

$$\forall ( n : \mathbb {N} ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {Perm}\left(l, \operatorname {range}\left(n\right)\right) \implies \forall ( t : \mathbb {N} ) , \operatorname {toFinset}\left(\operatorname {drop}\left(t, l\right)\right) = \operatorname {range}\left(n\right) \setminus \operatorname {toFinset}\left(\operatorname {take}\left(t, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.suffix_eq_undeleted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

For every time t, not merely an interior time, permutation membership and take/drop disjointness identify the suffix with precisely the undeleted set. This equality is consumed in both directions by generator_iff_exact.

**Definition 1.11 (Direct flip-to-zero chain).**

$$\forall ( n : \mathbb {N} ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {ExactGenerator}\left(n, l\right) \iff \operatorname {Perm}\left(l, \operatorname {range}\left(n\right)\right) \land \forall ( t : \mathbb {N} ) , t \le n \implies \operatorname {PN}\left(n, \operatorname {range}\left(n\right) \setminus \operatorname {toFinset}\left(\operatorname {take}\left(t, l\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.ExactGenerator` (`✓ std3`).

*Citation.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

This definition uses the actual set difference after each of the n+1 possible flip counts. No validity clause is supplied as an unproved structural premise.

**Theorem 1.12 (Equivalent chain coordinates).**

$$\forall ( n : \mathbb {N} ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {Generator}\left(n, l\right) \iff \operatorname {ExactGenerator}\left(n, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.generator_iff_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

The suffix/undeleted equality transports each chain comparison in both directions. It is consumed on the two endpoints and on every edge transported by result.

**Theorem 1.13 (The exact v1 event).**

$$\forall ( n : \mathbb {N} ) , \forall ( l : \operatorname {List}\left(\mathbb {N}\right) ) , \forall ( m : \operatorname {List}\left(\mathbb {N}\right) ) , \operatorname {ExactGenerator}\left(n, l\right) \implies \operatorname {ExactGenerator}\left(n, m\right) \implies \operatorname {ReflTransGen}\left(\operatorname {Edge}\left(\operatorname {ExactGenerator}\left(n\right)\right), l, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson; Moritz Dudey; Pamela Fleischmann; Annika Huch (2025). *Word Chain Generators for Prefix Normal Words*. DOI: [10.1007/978-3-032-09524-4_5](https://doi.org/10.1007/978-3-032-09524-4_5). URL: <https://arxiv.org/abs/2508.19619v1>.

*Commentary.*

ReflTransGen is the reflexive transitive closure, so the path is finite and may have zero moves. Every nontrivial edge has valid endpoints; the initial validity hypothesis also covers reflexivity. There is no restriction on direction, complexity, shortest paths or which sorting procedure a path must follow. The harmless n=0 extension does not replace any positive-n case.

The displayed names ReflTransGen, Perm, range, take, drop, toFinset, append, cons, erase and Ico denote their Lean operations. All new helpers lie on the result's live proof path. The generic sorting path, the suffix theorem and the final coordinate transport are proof support for this one question. Descending n,...,1 is a semantic valid generator: each state is an initial block of ones followed by zeros, so its prefix maximizes the count. No weighted-alphabet, directed reachability or efficient enumeration conclusion is asserted. The verified source scope and final-version limit are in the Library note; Lemma 17 is published supply, and the global construction is the retained application to the explicit v1 question.

## References

- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.Edge`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.ExactGenerator`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.Generator`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.PN`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.count`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.count_erase`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.erase_later_preserves`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.full_event_list`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.generator_ascent_swap`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.generator_iff_exact`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.normalize_by_adjacent_ascents`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.result`
- Truth anchor: `D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity.suffix_eq_undeleted`
