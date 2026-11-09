# Canonical representations and finite cardinality

## Abstract

Exact counting of actual binary-word near pairs

A physical binary word is a finite list of Boolean letters. The finite tree at height L consists of all such lists of length at most L. An unordered pair is an element of Sym2 of that list type; the distinctness condition excludes its diagonal. The distance is length(u)+length(v)-2*length(lcp(u,v)). BinaryWordGeometry.shortest_pop_append proves that this is the exact minimum number of literal right-end POP and APPEND edits, attained without exceeding the larger endpoint height.

**Definition 1.1 (Canonical pair representations).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Code`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An ancestor representation consists of a root word w, a Boolean b, and a suffix s, and represents the unordered pair of w and w followed by b::s. An opposite-branch representation consists of a root w and two suffix words s,t, and represents the unordered pair of w followed by false::s and w followed by true::t. These constructors retain every letter of the endpoints.

**Definition 1.2 (Common ancestor word).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.root`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root field is the actual longest common prefix of both represented endpoints, in either order.

**Definition 1.3 (First canonical endpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.left`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.left` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an ancestor representation this endpoint is the root itself. For an opposite-branch representation it is the word in the false child branch.

**Definition 1.4 (Second canonical endpoint).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.right`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.right` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an ancestor representation this endpoint extends the root by the nonempty suffix b::s. For an opposite-branch representation it is the word in the true child branch.

**Definition 1.5 (Exact endpoint edit distance).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.cost`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.cost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An ancestor representation has cost length(s)+1. An opposite-branch representation has cost length(s)+length(t)+2. Each is the common-prefix distance of its endpoints in either order.

**Definition 1.6 (Literal unordered endpoint pair).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.pair`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This maps a canonical representation to the Sym2 pair of its two actual word endpoints.

**Definition 1.7 (Distinct physical near pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Near`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Near` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L,D and unordered word pair p, Near(L,D,p) holds exactly when p has endpoint words u,v with u different from v, both lengths at most L, and common-prefix distance at most 2*D.

**Definition 1.8 (Height and distance cutoffs).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Valid`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L,D and representation c, validity requires both represented word lengths to be at most L and its exact cost to be at most 2*D.

**Theorem 1.9 (Existence and uniqueness for actual pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.canonical_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.canonical_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L,D, the map from canonical representations to actual unordered pairs is injective. For every unordered word pair p, Near(L,D,p) is equivalent to the existence of exactly one valid representation mapping to p. Existence removes equal initial letters recursively. At the first difference the Boolean letters determine the false and true branches; if one word ends first it becomes the ancestor endpoint. Uniqueness first recovers the root as the longest common prefix, and then cancels that prefix. A branch swap is impossible because false and true differ. Thus the fixed branch roles count an unordered pair exactly once.

**Definition 1.10 (Admissible positive branch depths).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.BranchIndex`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.BranchIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For remaining height t and budget D, the index consists of i,j less than t with i+j+2 at most 2*D. The physical branch depths are i+1 and j+1.

**Definition 1.11 (Finite endpoint data at a root).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.LocalData`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.LocalData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ancestor data choose d less than min(2*D,t), one Boolean, and a vector of d Boolean suffix letters. Their physical descendant depth is d+1. Branch data choose an admissible BranchIndex and suffix vectors of lengths i and j. The sum type distinguishes the ancestor and opposite-branch cases.

**Definition 1.12 (Finite representations over all roots).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.FiniteData`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.FiniteData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L,D, choose an index t less than L, a Boolean vector of length L-(t+1) for the actual root, and LocalData at remaining height t+1. No root can have depth L because the endpoints are distinct.

**Definition 1.13 (Bijection with physical near pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.physicalPairEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.physicalPairEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L,D, this equivalence maps FiniteData(L,D) bijectively onto the subtype of actual unordered word pairs satisfying Near(L,D). The forward map concatenates the literal vector letters to obtain the endpoints. The inverse recovers the root length, the remaining height, the case and the actual suffixes. No counting recurrence or representation assumption enters this equivalence.

**Definition 1.14 (Cardinality of actual physical pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.pairCount`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.pairCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L,D, pairCount(L,D) is Nat.card of the subtype of actual Sym2 word pairs satisfying Near(L,D). The finite-data equivalence proves that this subtype is finite.

**Definition 1.15 (Positive-depth sum).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.sourceSum`

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.sourceSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L,D, sum over t from 1 through L the product of 2^(L-t) with the following bracket: the sum of 2^d over d from 1 through min(2*D,t), plus the sum of 2^(i+j-2) over i,j from 1 through t satisfying i+j at most 2*D. All exponents and subtractions are natural numbers; positivity of i and j prevents exponent truncation.

**Theorem 1.16 (Exact distinct unordered near-pair count).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.exact_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.exact_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L,D, pairCount(L,D)=sourceSum(L,D). At remaining height t there are exactly 2^(L-t) actual root words. An ancestor descendant at depth d has 2^d possible suffix words. Opposite-branch endpoints at positive depths i,j have 2^(i-1)*2^(j-1)=2^(i+j-2) possible suffix pairs. The false and true roles have already fixed the orientation. The cardinality follows from the physical-pair bijection and finite sigma, product and vector cardinalities, then shifts the indices to the positive-depth ranges. L=0 and D=0 give empty sums, so both counts are zero; equal endpoints never occur.

This establishes the exact physical-pair identity IV.113 in section 39 of Recursive Relational Observation IV. Recorder injection IV.112, the estimate IV.114, the closed form IV.115 and resulting memory or update bounds require separate statements and proofs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.BranchIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Code`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.FiniteData`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.LocalData`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Near`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.Valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.canonical_representation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.cost`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.exact_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.left`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.pairCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.physicalPairEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.right`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.root`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs.sourceSum`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry](BinaryWordGeometry.md)
