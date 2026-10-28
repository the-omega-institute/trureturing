# The One-Common-Zeckendorf-Term Greedy Permutation

## Abstract

The least-unused one-common-Zeckendorf-term sequence is total and enumerates every positive integer exactly once.

OEIS A370630 asks whether the lexicographically earliest sequence of distinct positive integers whose consecutive canonical Zeckendorf expansions have exactly one common term is a permutation. The record is https://oeis.org/A370630/internal and its explicit selection rule is https://oeis.org/A370630/a370630.gp.txt. The source title is ‘Lexicographically earliest sequence of distinct positive integers such that the Zeckendorf expansions of two consecutive terms have exactly one common term.’ Its conjecture is ‘this sequence is a permutation of the positive integers.’ The record author is Rémy Sigrist; the conjecture comment has no separately signed attribution.

Fibonacci weights use F(0)=0, F(1)=1 and the usual additive recurrence. Only indices at least two occur in the canonical support. Thus the permitted weights are 1, 2, 3, 5, and so on, with no consecutive occupied indices. PARI bit position j represents Fibonacci index j+2. The comparison is numerical leastness among all unused positive integers. The overlap condition is cardinality exactly one.

**Definition 1.1 (Canonical Fibonacci support).**

$$(\forall m \in \mathbb{N},\; \operatorname{support}\left(m\right) = \operatorname{toFinset}\left(\operatorname{wdigits}\left(m\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing canonical W-digit equivalence supplies existence and uniqueness. The list stores Fibonacci indices, and passing to its finite set preserves precisely the occupied terms.

**Definition 1.2 (Exactly one shared canonical term).**

$$(\forall x \in \mathbb{N},\; (\forall y \in \mathbb{N},\; \operatorname{Adjacent}\left(x, y\right) \iff \operatorname{card}\left(\operatorname{inter}\left(\operatorname{support}\left(x\right), \operatorname{support}\left(y\right)\right)\right) = 1))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite-set intersection counts common Fibonacci terms in the unique nonadjacent representations.

**Definition 1.3 (The actual one-based sequence).**

$$(\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{v}\left(\operatorname{sub}\left(n, 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtraction on natural indices is truncated. Internally v(n) is the current value after n transitions from the initial history [1]. Each transition minimizes the positive integer absent from the entire history and adjacent to its current value, then prepends that integer. Consequently a(n+1)=v(n), and a(1)=1. The value at index zero is auxiliary; the assertion quantifies over positive indices.

**Definition 1.4 (The exact unused-successor predicate).**

$$(\forall s \in \mathbb{N} \to \mathbb{N},\; (\forall n \in \mathbb{N},\; (\forall m \in \mathbb{N},\; \operatorname{Eligible}\left(s, n, m\right) \iff (0 < m) \land ((\forall k \in \mathbb{N},\; ((1 \le k) \land (k \le n)) \Rightarrow (s\left(k\right) \neq m))) \land (\operatorname{Adjacent}\left(s\left(n\right), m\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.Eligible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every positive index from one through the current index belongs to the excluded prefix. A candidate must be positive and share exactly one canonical term with the current value.

**Definition 1.5 (Whole totality and permutation).**

$$(\forall s \in \mathbb{N} \to \mathbb{N},\; \operatorname{IsGreedyPermutation}\left(s\right) \iff (s\left(1\right) = 1) \land ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (0 < s\left(n\right)))) \land ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((\operatorname{Eligible}\left(s, n, s\left(\operatorname{add}\left(n, 1\right)\right)\right)) \land ((\forall m \in \mathbb{N},\; (\operatorname{Eligible}\left(s, n, m\right)) \Rightarrow (s\left(\operatorname{add}\left(n, 1\right)\right) \le m)))))) \land ((\forall i \in \mathbb{N},\; (\forall j \in \mathbb{N},\; ((1 \le i) \land (1 \le j) \land (s\left(i\right) = s\left(j\right))) \Rightarrow (i = j)))) \land ((\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\exists n \in \mathbb{N},\; (1 \le n) \land (s\left(n\right) = m))))))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.IsGreedyPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate includes the initial term, positivity, an eligible actual successor at every stage, leastness against every eligible candidate, injectivity on positive indices, and attainment of every positive integer.

**Theorem 1.6 (A370630 is a positive-integer permutation).**

$$(\operatorname{a}\left(1\right) = 1) \land ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (0 < \operatorname{a}\left(n\right)))) \land ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((\operatorname{Eligible}\left(\operatorname{a}, n, \operatorname{a}\left(\operatorname{add}\left(n, 1\right)\right)\right)) \land ((\forall m \in \mathbb{N},\; (\operatorname{Eligible}\left(\operatorname{a}, n, m\right)) \Rightarrow (\operatorname{a}\left(\operatorname{add}\left(n, 1\right)\right) \le m)))))) \land ((\forall i \in \mathbb{N},\; (\forall j \in \mathbb{N},\; ((1 \le i) \land (1 \le j) \land (\operatorname{a}\left(i\right) = \operatorname{a}\left(j\right))) \Rightarrow (i = j)))) \land ((\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow ((\exists n \in \mathbb{N},\; (1 \le n) \land (\operatorname{a}\left(n\right) = m)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fresh sufficiently large Fibonacci index pairs with an occupied index of the current term. Its weight exceeds the entire used prefix, so an unused eligible successor always exists. Well-ordering selects the least one. The full history therefore defines a single total sequence, and choosing outside it proves distinctness. For any omitted positive target, every visited neighbor would force the next actual term to be no larger than that target. Injectivity makes the sequence eventually larger than every fixed bound, so unbounded visited neighbors force coverage. To obtain such neighbors, consider the first stage whose support contains an index above an arbitrary bound. Let j be the largest new index and i the unique shared old index. The canonical pair {i,j} is unused and eligible. Its value is at most the actual next term, while greedy leastness gives the opposite inequality. Hence these arbitrarily large record terms are pairs. If a record pair has smaller index i at least four, the canonical pair {2,i}, of value F(i)+1, must be visited. If omitted, it bounds the next choice. The weight F(j) is too large to occur there, so the next term contains i and has value either F(i) or F(i)+1. The latter covers the target immediately. In the former case F(i) is then used, and one more greedy comparison forces F(i)+1. Either one smaller record index roots pairs with arbitrarily large second index, or finite cutoffs for each fixed smaller index force arbitrarily large distinct smaller indices. The preceding two-step argument then gives arbitrarily large visited pairs rooted at two. Thus some index r roots unbounded visited pairs. Any target containing r is adjacent to all sufficiently distant such pairs, so every such target occurs. Call this the hub property. If s is nonadjacent to a hub r, fresh canonical triples {r,s,t} are visited and provide unbounded neighbors for every target containing s but not r; targets containing r are already covered. Hence s is a hub. For an arbitrary positive target, choose a hub s beyond its entire support and the first hub, and choose an occupied target index k. Fresh triples {s,k,t} are visited and intersect that target in exactly {k}. Unbounded-neighbor coverage finishes the proof. The argument uses all stages of the actual history-dependent minimum rule; no finite enumeration is a premise.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.Adjacent`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.Eligible`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.IsGreedyPermutation`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.a`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.support`
- Dependency: [D5/S0/Conventions/WDigits](../../../S0/Conventions/WDigits.md)
