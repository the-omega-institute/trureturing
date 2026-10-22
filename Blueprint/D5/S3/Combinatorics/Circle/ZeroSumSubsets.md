# Zero subsets of the physical circle source

## Abstract

Binary masks restrict how many exact integer-zero subsets and independent zero blocks an actual centered doubling source can have.

**Theorem 1.1 (The source gcd bounds the entire zero fibre).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; 3 \le k \Rightarrow \operatorname{card}\left(\operatorname{Z}\left(k, t\right)\right) \le \operatorname{gcd}\left(t, 2^{k} - 1\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ZeroSumSubsets.zero_subsets_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any natural number at least three, t any natural number, and N=2^k-1. The source is exactly SourceWidth.actualSource: at the physical label p in Fin(k), take the integer centered representative of t times 2^p modulo N. The centered interval is [-floor(N/2),floor(N/2)]. Cyclic doubling supplies these arithmetic residues; the count concerns their exact integer sums. Equal numerical values at different positions remain different labels.

Write Z for all finsets A of Fin(k) whose source values sum to the integer zero. Thus Z ranges over every physical-label finset satisfying that equality. Then card(Z) is at most gcd(t,N)+1. There is no unit, distinct-value or full-period assumption.

Encode A by the natural binary mask M(A)=sum over p in A of 2^p. Colexicographic binary-sum injectivity makes M injective on physical subsets. Every mask lies in [0,N], including the empty mask zero and the full mask N. Each centered value is congruent to t times 2^p modulo N. Summing these congruences shows that integer zero forces N to divide t M(A).

Put g=gcd(t,N) and Q=N/g. Since N is positive, g and Q are positive. Cancel g, then use coprimality of t/g and N/g: Q divides every zero-subset mask. The quotient M(A)/Q is therefore an integer in [0,g]. It still determines A, because multiplication by Q recovers M(A). This injection into g+1 integers proves the bound. The same cancellation includes t=0: g=N and Q=1, so all binary masks remain allowed.

Mask divisibility is used only as a necessary condition. A mask with Q dividing M(A) need not have exact integer source sum zero: congruence modulo N cannot detect a nonzero multiple of N. The argument counts a superset of the integer-zero fibre and does not replace that fibre by a congruence class.

**Theorem 1.2 (Independent zero blocks consume exponentially many masks).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall blocks \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)\right),\; 3 \le k \Rightarrow \left(\left(\left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{mem}\left(A, blocks\right) \Rightarrow \operatorname{Nonempty}\left(A\right)\right) \land \left(\operatorname{PairwiseDisjoint}\left(blocks\right) \land \left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{mem}\left(A, blocks\right) \Rightarrow \operatorname{sum}\left(A, \operatorname{actualSource}\left(k, t\right)\right) = 0\right)\right)\right) \Rightarrow 2^{\operatorname{card}\left(blocks\right)} \le \operatorname{gcd}\left(t, 2^{k} - 1\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ZeroSumSubsets.disjoint_zero_blocks_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family blocks of nonempty, pairwise disjoint physical-label finsets, assume each block has exact integer source sum zero. Then 2 raised to card(blocks) is at most gcd(t,N)+1. The family need not cover all labels; a partition of the entire source is a special case. The empty family is also allowed.

Every subfamily has a union with exact sum zero, by disjoint-union sum additivity. Distinct subfamilies have distinct unions: choose a label in a block belonging to one subfamily, and disjointness forces any block covering that label in the other subfamily to be the same block. Thus the 2^b subfamilies inject into Z. Combining this injection with the source count gives the restriction.

For a unit source g=1, this permits at most one nonempty zero block. More generally, any proposed splitting into b independent zero pieces must satisfy the exponential bound, even when source values repeat or have a short period. A construction based on freely choosing arbitrarily many independent integer-zero pieces therefore has an arithmetic obstruction. Existence of such a decomposition is not an assumption about the source in the count theorem.

The source motivation is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. These are necessary restrictions on exact zero subsets and decompositions. They do not construct a permutation with every prefix in [0,(N-1)/2]. The full all-source capacity-C conclusion remains open; collective splitting and interleaving with nonzero block charges is not controlled by this count. No claim of literature novelty is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ZeroSumSubsets.disjoint_zero_blocks_bound`
- Truth anchor: `D5/S3/Combinatorics/Circle/ZeroSumSubsets.zero_subsets_card_le`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
