# Ordinary coloured occupation coordinates

## Abstract

Ordinary positive-mode occupations and finite coloured partitions

For every number r of colours and every energy N, an occupation assigns natural multiplicities to pairs (i,n) in Fin r times the natural numbers, with finite support and weight n+1. Every positive integer frequency occurs. The construction includes no colours, zero energy and empty support.

**Definition 1.1 (The full positive-mode energy fibre).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOccupation.OccupationFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOccupation.OccupationFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OccupationFiber r N consists of all finitely supported occupations d on Fin r times the natural numbers with Finsupp.weight (fun x => x.2+1) d = N. The mode index is unbounded and there is no odd-mode restriction.

**Definition 1.2 (An explicit equivalence with coloured partitions).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOccupation.occupationPartitionEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOccupation.occupationPartitionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all r,N : Nat, occupationPartitionEquiv r N has type OccupationFiber r N equivalent to ColouredEulerLedger.ColouredPartition (fun _ => r) N. Forgetting colours gives a one-colour occupation, and the existing PolynomialFockCharacter.energyFiberEquivPartition sends it to a partition. For each occurring positive part k, the multiplicities d(i,k-1) form a colour allocation whose sum is the multiplicity of k. Mathlib's Sym.equivNatSumOfFintype converts each allocation to the corresponding multiset of colours.

The inverse sums Finsupp.single (i,k-1) with the allocated multiplicity, over the finitely many occurring parts k and all colours i. Positivity of partition parts makes k-1 the inverse of the frequency n+1. The count_mode identity proves that forgetting colours records precisely the sum of the colour multiplicities. Evaluation at an occurring part recovers its allocation; outside the partition support it is zero. The weight sum equals N, so the inverse lies in the original energy fibre.

The two inverse proofs establish equality of the original occupations and of the dependent partition-and-colouring data. They use extensionality, equality of partition part counts, and heterogeneous equality for allocations with dependent multiplicities. These are actual inverse fields of the equivalence. No positive-energy, nonempty-colour or nonempty-support premise is added.

The one-colour partition map is reused from PolynomialFockCharacter, the coloured-partition carrier from ColouredEulerLedger, and the allocation carrier from ColouredOddMultiplicity. Only the allocation carrier is shared with the odd-mode construction: the weights here are all ordinary positive integers. The project suppliers, Mathlib and Batteries retain their authorship and licenses. This is a repository-derived construction on those carriers; no literature novelty is claimed.

This equivalence supplies occupation coordinates for the ordinary coloured-partition count used in lattice physical characters. It does not identify a BRST quotient or a physical charge fibre by itself; those require their separate cohomology and physical-realization proofs.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOccupation.OccupationFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOccupation.occupationPartitionEquiv`
- Dependency: [D5/S3/Combinatorics/Partitions/ColouredEulerLedger](ColouredEulerLedger.md)
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockCharacter](../../VertexAlgebra/PolynomialFockCharacter.md)
