# Composite Concatenations of Distinct Partition Parts

## Abstract

The only positive indices without an eligible composite concatenation are one, two, and four.

OEIS A110454 considers every ordering of the pairwise distinct positive parts of a partition and concatenates the ordered parts in base ten. Single-part partitions are included, and an eligible value is greater than four and composite.

Natural-number digit lists are little-endian. Reversing the list of parts before flat-mapping their digit lists therefore makes ofDigits read the parts from left to right.

**Definition 1.1 (Decimal concatenation).**

$$\forall parts \in List\left(Nat\right),\; decimalConcatenation\left(parts\right) = ofDigits\left(10, flatMap\left(digits\left(10\right), reverse\left(parts\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.decimalConcatenation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reversed list of parts is replaced by the base-ten digits of each part, then ofDigits evaluates the resulting little-endian digit list.

**Definition 1.2 (All distinct-partition concatenations).**

$$\forall n \in Nat,\; C\left(n\right) = biUnion\left(filter\left(powerset\left(erase\left(range\left(n + 1\right), 0\right)\right), (parts \mapsto sum\left(parts, id\right) = n)\right), (parts \mapsto image\left(decimalConcatenation, toFinset\left(permutations\left(sort\left(parts\right)\right)\right)\right))\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Start with the positive integers below or equal to n, take every subset whose sum is n, then take every permutation of its sorted list and map decimalConcatenation over those permutations. Thus the parts are pairwise distinct positive integers summing to n, and every ordering is taken.

**Theorem 1.3 (Murthy's conjecture).**

$$\left(\forall n \in Nat,\; 1 \le n \Rightarrow \left(\left(\neg (n \in \left\{1, 2, 4\right\})\right) \Rightarrow \left(\exists m \in C\left(n\right),\; 4 < m \land \left(\neg Prime\left(m\right)\right)\right)\right)\right) \land \left(\forall n \in \left\{1, 2, 4\right\},\; filter\left(C\left(n\right), (m \mapsto 4 < m \land \left(\neg Prime\left(m\right)\right))\right) = \emptyset\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.murthy_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a110454-distinct-partition-concatenation-zero-indices` (proved) by `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.murthy_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a110454-distinct-partition-concatenation-zero-indices","declaration_gid":"D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.murthy_conjecture","resolution_kind":"proved"} -->

*Citation.* Amarnath Murthy (2005). *OEIS A110454, Largest composite number obtained by concatenation of parts of a distinct partition of n*. URL: <https://oeis.org/A110454>.

*Commentary.*

For n=3, the ordered parts two and one give 21. For n at least five, the ordered parts n-2 and two give 10(n-2)+2=2(5n-9), an even value greater than four. Direct classification at one, two, and four shows that their eligible filters are empty.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.C`
- Truth anchor: `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.decimalConcatenation`
- Truth anchor: `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.murthy_conjecture`
