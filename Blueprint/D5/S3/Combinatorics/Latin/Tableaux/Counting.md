# Counting for Latin tableaux

## Abstract

Literal source Latin tableaux: Counting

Daugherty et al., arXiv:2610.29291v1, Conjecture 6.3 asks for the full count of Latin tableaux of shape (k,k-1,...,5,4,3,3) for every integer k at least five. Cells and integer symbols retain their fixed identities, and the prescribed symbol multiplicities are those of the conjugate partition.

**Definition 1.1 (Literal column compatibility).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.ColumnDisjoint`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Counting.ColumnDisjoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Compare entries only at the same actual column index, allowing absent cells in shorter rows.

**Definition 1.2 (Actual row lists).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.RawLatin`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Counting.RawLatin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Each row is a permutation of its exact initial symbol interval, and all row pairs satisfy column compatibility.

**Definition 1.3 (Availability for the next longest row).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.available`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Counting.available` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

At each fixed column retain exactly those symbols not already present there.

**Definition 1.4 (Complete finite enumeration).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.enumerate`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Counting.enumerate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Recursively prepend every matching of the actual availability graph to every smaller tableau. Distinct tails give disjoint extension sets.

**Theorem 1.5 (Enumeration is exact).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.mem_enumerate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.mem_enumerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Proves both directions between enumeration membership and literal compatible row permutations.

**Definition 1.6 (The zero-based row representation).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.rowsOf`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Counting.rowsOf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Read all finite-source rows in their actual order, with zero-based values; the source equivalence restores actual integer labels by adding one.

**Definition 1.7 (Every source filling appears exactly once).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.enumerationEquiv`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/Counting.enumerationEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The explicit inverse row construction composes with sourceEquiv, producing a reversible bijection from all source tableaux to enumeration members.

**Theorem 1.8 (Equality of literal counts).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.source_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.source_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The algorithm counts exactly the unrestricted source tableaux, with no isotopy, reduction, or symmetry identification.

**Theorem 1.9 (Actual shape growth).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.shape_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.shape_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

For every k at least five the next source diagram is obtained by prepending its actual row of length k+1.

**Theorem 1.10 (The complete base at k=5).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.base_count_and_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.base_count_and_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Kernel decision checks all tableaux of (5,4,3,3): there are 144, and every one has the full next-row invariant with low symbols {0,1,2} and high symbols 3,4,5. The smaller (4,3,3) layer cannot supply a uniform fourfold transition.

**Theorem 1.11 (No missing induction hypotheses).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.universal_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.universal_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Induction proves the full invariant for every tableau at every k at least five. The availability-update identity is proved using actual row bounds. No transition, invariant, enumeration, or coverage assumption is left in the result.

**Theorem 1.12 (Exactly four extensions for every tableau).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.count_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.count_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Every invariant graph has four distinct matchings; prepending to different tails gives disjoint sets. This proves the count recurrence rather than assuming it.

**Theorem 1.13 (The complete universal count).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

For every natural k at least five, the full source count is 9 times 4 to the power k-3. The proof combines the exact source bijection, checked complete base, and proved all-parameter transition.

**Theorem 1.14 (Conjecture 6.3 over every integer k at least five).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63_integer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63_integer` (`✓ std3`). ∎

*Resolves.* `Problems/daugherty-latin-tableaux-conjecture63` (proved) by `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63_integer`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"daugherty-latin-tableaux-conjecture63","declaration_gid":"D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63_integer","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

For every integer k at least five, LT of its natural value is 9 times 4 to the power k.toNat-3. In this domain conversion is exact, and the shape is precisely the source shape. This is the full source assertion, not a bounded check or weaker existence statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.ColumnDisjoint`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.RawLatin`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.available`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.base_count_and_invariant`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.conjecture63_integer`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.count_step`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.enumerate`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.enumerationEquiv`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.mem_enumerate`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.rowsOf`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.shape_succ`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.source_enumeration`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/Counting.universal_invariant`
- Dependency: [D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate](MatchingTemplate.md)
- Dependency: [D5/S3/Combinatorics/Latin/Tableaux/Source](Source.md)
