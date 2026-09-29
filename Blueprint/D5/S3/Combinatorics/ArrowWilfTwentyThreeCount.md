# Decorated Objects for the Second Pattern

## Abstract

A lower derangement prefix and a decreasing upper skeleton enumerate avoiders with a prescribed smallest fixed point.

**Definition 1.1 (Decorated data with a smallest fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.TwentyThreeData`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.TwentyThreeData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Choose r lower values R, a word rho on R, a no-fixed-point word sigma on the remaining lower values, and a weak gap composition of r indexed by the values above m.

**Definition 1.2 (The decreasing upper skeleton).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperDescending`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperDescending` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The upper word is n down through m plus one in decreasing order.

**Definition 1.3 (Read upper gaps in skeleton order).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperGapSizes`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperGapSizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The list reads each labelled upper gap in the order n down through m plus one.

**Theorem 1.4 (Length and sum of upper gaps).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperGapSizes_length_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperGapSizes_length_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The upper gap list has n minus m entries, and their sum is r.

**Definition 1.5 (The decorated output word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Concatenate the no-fixed lower prefix, m, and the decreasing upper skeleton with consecutive blocks of rho inserted after its entries.

**Theorem 1.6 (The output uses each value once).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When one at most m at most n, every decorated output permutes the standard support from one through n.

**Theorem 1.7 (The distinguished value is fixed).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_fixed_m`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_fixed_m` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For m strictly below n, hat fixes m in the decorated output.

**Theorem 1.8 (A larger suffix preserves singleton syntax).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_append_greater_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_append_greater_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For g below m appearing in a prefix u, appending m and a suffix leaves FixedSyntax g equivalent to its status in u.

**Theorem 1.9 (A lower singleton lies in the prefix).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_append_greater_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_append_greater_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If g below m has singleton syntax in a word split before m, then g occurs in the prefix before m.

**Theorem 1.10 (No smaller value is fixed).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_no_lower_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_no_lower_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

No value g below m occurring in a decorated output is fixed by hat.

**Theorem 1.11 (Recovering the upper skeleton).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.filter_twentyThreeList_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.filter_twentyThreeList_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Filtering a decorated output for values greater than m yields the decreasing upper skeleton.

**Theorem 1.12 (Upper entries cannot increase).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.no_increasing_upper_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.no_increasing_upper_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If m is below a and a is below b, the ordered pair a,b is not a sublist of a decorated output.

**Theorem 1.13 (The decorated output avoids the second pattern).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For positive m below n, the decorated word does not contain (23; 1 to 1).

**Definition 1.14 (The output as an avoiding word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeAvoider`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeAvoider` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Package the decorated list as a word on the standard support that avoids the second pattern.

**Definition 1.15 (The independent decorated choices).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeDataEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeDataEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The data type is equivalent to the dependent sum over R of a word on R, a no-fixed-point word on its lower complement, and an upper-labelled gap vector.

**Theorem 1.16 (The decorated summand count).**

$$\forall n \in \mathrm{Nat}, m \in \mathrm{Nat}, r \in \mathrm{Nat},\; \operatorname{card}\left(\operatorname{TwentyThreeData}\left(n, m, r\right)\right) = \operatorname{choose}\left(m - 1, r\right) \cdot \operatorname{choose}\left(n - m + r - 1, r\right) \cdot \operatorname{factorial}\left(r\right) \cdot \operatorname{numDerangements}\left(m - 1 - r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.card_twentyThreeData` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The cardinality is choose(m minus one,r) times choose(n minus m plus r minus one,r) times r factorial times the derangement number at m minus one minus r.

**Definition 1.17 (The exceptional top fiber).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.TopAvoiders`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.TopAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

These avoiding words fix n and have no hat-fixed value below n.

**Definition 1.18 (The top fiber has an exact fixed set).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.topAvoidersEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.topAvoidersEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For positive n, the exceptional top fiber is equivalent to words whose exact hat-fixed set is the singleton containing n.

**Theorem 1.19 (Decomposing an arbitrary word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.interleave_decompose`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.interleave_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Any word splits into an initial filler block and later filler blocks after the entries satisfying a Boolean skeleton predicate.

**Theorem 1.20 (Avoidance forces the upper order).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upper_filter_eq_of_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upper_filter_eq_of_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For an avoiding word fixed at m, filtering values above m gives the unique decreasing upper skeleton.

**Theorem 1.21 (Splitting at an occurring value).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.split_at_member`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.split_at_member` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Every list containing x can be written as a prefix followed by x and a suffix.

**Theorem 1.22 (Structure around a singleton block).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When m is absent from a prefix and has singleton syntax at the following position, all prefix entries are below m and the suffix is empty or begins above m.

**Theorem 1.23 (No initial filler before a skeleton head).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.interleave_decompose_head`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.interleave_decompose_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If the first entry satisfies the skeleton predicate, the interleaving decomposition has no initial filler block.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.TopAvoiders`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.TwentyThreeData`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.card_twentyThreeData`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.filter_twentyThreeList_upper`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_append_greater_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_append_greater_mem`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.fixedSyntax_split`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.interleave_decompose`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.interleave_decompose_head`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.no_increasing_upper_pair`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.split_at_member`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.topAvoidersEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeAvoider`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeDataEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_avoids`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_fixed_m`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_no_lower_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.twentyThreeList_perm`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperDescending`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperGapSizes`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upperGapSizes_length_sum`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.upper_filter_eq_of_avoids`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveCount](ArrowWilfTwelveCount.md)
