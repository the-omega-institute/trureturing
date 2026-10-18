# Coloured Odd Occupation

## Abstract

Odd-weight occupations are odd-part partitions with dependent finite-colour energy allocations, giving exact convolution and a formal Euler product.

The variable X counts twice the half-integer oscillator energy. All finite colour types, including the empty type, and every degree are included. The coefficient identity holds over an arbitrary commutative semiring. Only the infinite-product statements use a field and its T2 topological-ring structure, with the coefficient topology on formal power series.

**Definition 1.1 (Odd mode weights).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.oddWeight`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.oddWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural mode n, oddWeight(n)=2*n+1. These are positive odd parts, and this weight already counts twice the half-integer oscillator energy.

**Definition 1.2 (Single-colour weighted energy).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.singleEnergy`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.singleEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finitely supported occupation d:N -> N, singleEnergy(d) is the sum of d(n)*(2*n+1). There is no support cutoff beyond finite support of each occupation.

**Definition 1.3 (The complete single-colour fibre).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.SingleOddFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.SingleOddFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N:N, SingleOddFiber(N) consists of all finitely supported natural occupations whose singleEnergy is N.

**Definition 1.4 (Odd-part partitions).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.OddPartition`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.OddPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N:N, OddPartition(N) is the element type of Mathlib Nat.Partition.odds N, the finite set of partitions of N whose parts are all odd.

**Definition 1.5 (Invert odd parts by integer division).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.singleOddFiberEquivPartition`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.singleOddFiberEquivPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N:N, SingleOddFiber(N) is equivalent to OddPartition(N). The forward map repeats 2*n+1 with multiplicity d(n). The inverse maps each odd part j to j/2 and counts these mode indices. Positivity and odd membership give 2*(j/2)+1=j; multiset injectivity proves the other inverse. The Finsupp and multiset architecture is the one used for ordinary positive parts in PolynomialFockCharacter.energyFiberEquivPartition, with this different inverse and restricted codomain.

**Definition 1.6 (Finite-colour occupation energy).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredEnergy`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every type I and occupation d:(I times N) -> N of finite support, colouredEnergy(I,d) is the weighted sum with weight 2*n+1 on a pair (i,n). I may be empty.

**Definition 1.7 (Unbounded coloured fibre).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.ColouredOddFiber`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.ColouredOddFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every type I and natural N, ColouredOddFiber(I,N) is the subtype of all finitely supported occupations d with colouredEnergy(I,d)=N. All modes and occupation multiplicities are allowed.

**Definition 1.8 (Currying by colour).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colourEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colourEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I, Mathlib Finsupp.curryEquiv followed by Finsupp.equivFunOnFinite identifies occupations on I times N with functions I -> (N -> finitely-supported N).

**Theorem 1.9 (Energy splits over colours).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredEnergy_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredEnergy_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite type I and occupation d, colouredEnergy(I,d) equals the sum over i:I of singleEnergy(colourEquiv(I,d)(i)). This follows from the public Finsupp.sum_curry_index and Finsupp.sum_fintype identities.

**Definition 1.10 (Dependent colour energies).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.EnergyAllocation`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.EnergyAllocation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I and N:N, EnergyAllocation(I,N) consists of functions e:I -> N whose finite sum is N.

**Definition 1.11 (Odd partitions with dependent energies).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.OddPartitionSigma`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.OddPartitionSigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I and N:N, OddPartitionSigma(I,N) is the dependent sum over energy allocations e of the product over i:I of OddPartition(e(i)).

**Definition 1.12 (Pointwise energy fibres).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.pointwiseEnergyFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.pointwiseEnergyFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every type I and e:I -> N, the subtype of functions f:I -> (N -> finitely-supported N) with pointwise singleEnergy equal to e is equivalent to the dependent product over i of SingleOddFiber(e(i)). Mathlib subtypePiEquivPi supplies the pointwise subtype transport.

**Definition 1.13 (The full dependent coloured equivalence).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredOddFiberEquivSigma`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredOddFiberEquivSigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I, including the empty type, and every N:N, ColouredOddFiber(I,N) is equivalent to OddPartitionSigma(I,N). Currying splits the actual weighted energy, sigmaSubtypeFiberEquivSubtype groups by the entire energy allocation, and the single-colour inverse is applied in every dependent fibre.

**Definition 1.14 (The exact finite antidiagonal).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.energyAllocationEquivAntidiag`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.energyAllocationEquivAntidiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite decidable type I and N:N, EnergyAllocation(I,N) is equivalent to the element type of univ.finsuppAntidiag(N). The maps are Finsupp.equivFunOnFinite and evaluation, with the same sum N and full finite support condition.

**Definition 1.15 (Occupation fibres match convolution indices).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredOddFiberEquivAntidiag`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredOddFiberEquivAntidiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite decidable type I and N:N, the complete occupation fibre is equivalent to the dependent sum over univ.finsuppAntidiag(N) of the products of OddPartition(e(i)). This finite sigma type also gives genuine finiteness of the original fibre.

**Theorem 1.16 (Exact all-degree cardinal convolution).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.card_colouredOddFiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.card_colouredOddFiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable type I and N:N, Nat.card(ColouredOddFiber(I,N)) is the sum over e in univ.finsuppAntidiag(N) of the product over i:I of card(Nat.Partition.odds(e(i))). The equivalence with a finite dependent sigma proves the cardinal formula; no infinite-type default for Nat.card is used.

**Definition 1.17 (One-colour partition series).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.oddPartitionSeries`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.oddPartitionSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every commutative semiring R, oddPartitionSeries(R) is the formal power series whose coefficient of degree N is card(Nat.Partition.odds N), cast into R.

**Definition 1.18 (The occupation counting series).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries`

*Formalization.* `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every commutative semiring R and finite type I, colouredFiberSeries(R,I) has degree N coefficient Nat.card(ColouredOddFiber(I,N)), cast into R.

**Theorem 1.19 (Coefficient convolution identifies the series).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries_eq_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative semiring R and finite type I, colouredFiberSeries(R,I) equals the product over I of oddPartitionSeries(R). The exact fibre cardinal sum is the finite antidiagonal in Mathlib PowerSeries.coeff_prod. This is an algebraic coefficient identity and needs no topology.

**Theorem 1.20 (Equal factors give a finite power).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries_eq_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries_eq_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative semiring R and finite type I, colouredFiberSeries(R,I) equals oddPartitionSeries(R) raised to Fintype.card(I). The empty product is included. This finite-product identity is used in the Euler product theorem.

**Theorem 1.21 (The formal geometric inverse).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.odd_geometric_eq_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.odd_geometric_eq_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field with a T2 topology making it a topological ring. For every n:N, the formal sum over j:N of X^((2*n+1)*j) equals the power-series inverse of 1-X^(2*n+1). Its constant term is one, and Mathlib formal geometric summation proves the multiplication identity. PowerSeries K is not assumed to be a field.

**Theorem 1.22 (Restricted-partition formal product).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.hasProd_oddPartitionSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.hasProd_oddPartitionSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field with a T2 topology making it a topological ring. In PowerSeries.WithPiTopology, the factors (1-X^(2*n+1)) inverse have HasProd oddPartitionSeries(K). Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted is restricted to odd positive parts, its inactive factors are one, and injective reindexing by n -> 2*n gives the stated family. The restricted-partition supplier is due to Weiyi Wang in Mathlib under Apache 2.0.

**Theorem 1.23 (The complete finite-colour formal Euler product).**

Lean statement: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.hasProd_colouredFiberSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.hasProd_colouredFiberSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field with a T2 topology making it a topological ring, and let I be any finite type. In PowerSeries.WithPiTopology, the factors ((1-X^(2*n+1)) inverse) raised to card(I) have HasProd colouredFiberSeries(K,I). The coefficient-convolution identity identifies the target with the corresponding power of the one-colour partition series. HasProd supplies Multipliable before any tprod equality is deduced. Empty colours are included. No analytic evaluation, eta transformation, modularity or physical completion is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.ColouredOddFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.EnergyAllocation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.OddPartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.OddPartitionSigma`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.SingleOddFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.card_colouredOddFiber`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colourEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredEnergy`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredEnergy_eq_sum`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries_eq_pow`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredFiberSeries_eq_prod`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredOddFiberEquivAntidiag`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.colouredOddFiberEquivSigma`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.energyAllocationEquivAntidiag`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.hasProd_colouredFiberSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.hasProd_oddPartitionSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.oddPartitionSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.oddWeight`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.odd_geometric_eq_inverse`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.pointwiseEnergyFiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.singleEnergy`
- Truth anchor: `D5/S3/Combinatorics/Partitions/ColouredOddOccupation.singleOddFiberEquivPartition`
