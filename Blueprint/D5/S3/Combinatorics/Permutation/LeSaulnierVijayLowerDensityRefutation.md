# Refutation of the LeSaulnier-Vijay lower-density conjecture

## Abstract

A staged set of positive integers admits a progression-free permutation and has lower density at least four fifteenths, exceeding one quarter.

**Definition 1.1 (Progression-free enumeration).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.ThreeFree`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.ThreeFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a subset T of the natural numbers, ThreeFree(T) means there exists a map pi from the natural numbers to the natural numbers which is injective, has range exactly T, and satisfies pi(i)+pi(k) unequal to 2*pi(j) for every triple of natural indices i<j<k. The equation covers progressions in both numerical directions. The map is an enumeration of the entire infinite set; finite sets do not satisfy this definition.

**Definition 1.2 (Lower asymptotic density).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.lowerDensity`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.lowerDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a subset T of the natural numbers, lowerDensity(T) is the real-valued Filter.liminf, along Filter.atTop on natural n, of the cardinality of T intersected with the inclusive interval [1,n], cast to the reals and divided by n. This is the source's lower density for positive integers. The single term n=0 does not affect the limit inferior.

**Definition 1.3 (The conjectured quarter-density bound).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim states: for every subset T of the natural numbers, if zero is not in T and ThreeFree(T) holds, then lowerDensity(T) is at most one quarter. This is the upper-bound content of the conjecture beta(3)=1/4, together with the paper's established lower bound beta(3)>=1/4.

**Theorem 1.4 (The quarter-density conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lesaulnier-vijay-2011-beta3-lower-density` (refuted) by `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lesaulnier-vijay-2011-beta3-lower-density","declaration_gid":"D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Let M(k)=(11^k+1)/2. The counterexample is the singleton {1} together with, for each natural k, both inclusive intervals [2*M(k),3*M(k)-1] and [6*M(k)-2,11*M(k)-5]. Every arithmetic progression in this set lies in one stage. Within a stage, the binary-reversal rank places the middle term of every three-term progression before both endpoints or after both. Disjoint increasing rank ranges order the stages; enumerating the infinite rank image gives the literal injective permutation required by ThreeFree. The counting bound 15*card(S intersect [1,n])>=4*n for every n>=1 gives lowerDensity(S) >=4/15. Since 4/15>1/4 and zero is absent, the conjectured universal bound contradicts this explicit example.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.ThreeFree`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.lowerDensity`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.result`
- Dependency: [D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity](LeSaulnierVijayLowerDensityRefutationDensity.md)
- Dependency: [D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationEnumeration](LeSaulnierVijayLowerDensityRefutationEnumeration.md)
- Dependency: [D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder](LeSaulnierVijayLowerDensityRefutationOrder.md)
