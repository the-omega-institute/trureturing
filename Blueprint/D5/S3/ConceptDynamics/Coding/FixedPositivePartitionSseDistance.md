# Fixed positive partition exchange distance

## Abstract

The fixed positive group-ring partition family has exact maximum-coordinate exchange distance.

**Theorem 1.1 (The entire fixed partition family).**

$$\forall H: Type, [\operatorname{Group}\left(H\right)], [\operatorname{Fintype}\left(H\right)], [\operatorname{Nontrivial}\left(H\right)], \forall n: Nat, \forall p: \operatorname{Partition}\left(n\right), \forall r: \operatorname{Partition}\left(n\right), 1 \le n \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{partitionMatrix}\left(H, p\right), \operatorname{partitionMatrix}\left(H, r\right), \operatorname{dInf}\left(p, r\right)\right)\right) \land (\forall L: Nat, \operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{partitionMatrix}\left(H, p\right), \operatorname{partitionMatrix}\left(H, r\right), L\right) \Rightarrow \operatorname{dInf}\left(p, r\right) \le L)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.theorem32_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite nontrivial group, q its order, u the sum of its group elements, and write z(H)=q1-u in the integer group ring. Here smul denotes natural-number scalar multiplication, and toNat converts each integer coefficient to a natural number. A partition p of n is padded to n decreasing coordinates. Its nilpotent shift is the direct sum of the upper Jordan shifts of these lengths, flattened by prefix sums. Thus the coordinates and endpoint depend only on p.

$\forall H: Type, [\operatorname{Group}\left(H\right)], [\operatorname{Fintype}\left(H\right)], \operatorname{z}\left(H\right) = \operatorname{smul}\left(\operatorname{card}\left(H\right), 1\right) - \operatorname{uniform}\left(H\right)$

$\forall H: Type, [\operatorname{Group}\left(H\right)], [\operatorname{Fintype}\left(H\right)], \forall n: Nat, \forall p: \operatorname{Partition}\left(n\right), \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), \operatorname{partitionMatrix}\left(H, p, i, j\right) = \operatorname{toNat}\left(\operatorname{smul}\left(\operatorname{power}\left(\operatorname{card}\left(H\right), 3\right) \cdot n, \operatorname{uniform}\left(H\right)\right) + \operatorname{smul}\left(\operatorname{card}\left(H\right) \cdot \operatorname{partitionShift}\left(p, i, j\right), \operatorname{z}\left(H\right)\right)\right)$

The displayed integer group-ring entries are strictly positive and hence determine natural group-ring entries. The baseline q cubed times n is fixed throughout the family.

For neighboring partitions, rectangular zero-one block factors P and Q multiply to their respective shifts. Empty blocks are allowed. Flattening uses the two independent prefix-sum coordinates. The group-ring factors U=qJu+Pz and V=qJu+Qz have strictly positive natural coefficients and their actual products are the two endpoints. The fixed-mass partition geodesic therefore gives a chain of the exact displayed length, including length zero.

For the lower bound, every competing rectangular chain supplies cumulative intertwining maps R and S whose two products are the endpoint powers of its length L. Intermediate dimensions may change and may be zero. Act on the kernel of rational augmentation, whose rational dimension is q-1. The uniform element annihilates this ideal, and the endpoint acts as q squared times its partition shift on each ideal coordinate.

For the endpoint operators T and Q, set I=im(T to the j), M=S(I), and N=im(T to the j+L). The map R from M onto N intertwines the restrictions. It induces an actual surjection from M/QM onto N/TN. Rank-nullity and the embedding of the kernel on M into the kernel on im(Q to the j) compare the endpoint layer dimensions.

$\forall V: Type, \forall W: Type, [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(Rational, V\right)], [\operatorname{FiniteDimensional}\left(Rational, V\right)], [\operatorname{AddCommGroup}\left(W\right)], [\operatorname{Module}\left(Rational, W\right)], [\operatorname{FiniteDimensional}\left(Rational, W\right)], \forall T: \operatorname{End}\left(Rational, V\right), \forall Q: \operatorname{End}\left(Rational, W\right), \forall R: \operatorname{LinearMap}\left(Rational, W, V\right), \forall S: \operatorname{LinearMap}\left(Rational, V, W\right), \forall L: Nat, \left(\operatorname{comp}\left(T, R\right) = \operatorname{comp}\left(R, Q\right) \land \left(\operatorname{comp}\left(Q, S\right) = \operatorname{comp}\left(S, T\right) \land \operatorname{comp}\left(R, S\right) = \operatorname{power}\left(T, L\right)\right)\right) \Rightarrow (\forall j: Nat, \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(T, j + L\right)\right)\right) - \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(T, j + L + 1\right)\right)\right) \le \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(Q, j\right)\right)\right) - \operatorname{finrank}\left(Rational, \operatorname{range}\left(\operatorname{power}\left(Q, j + 1\right)\right)\right))$

Explicit endpoint shift coordinates evaluate each layer as q-1 times the number of partition parts exceeding its threshold. Cancel q-1, which is positive. Taking j equal to each part of the opposite partition proves the coordinate bound in both directions. Their maximum gives the lower bound on every chain length. No classification or partition assumption is imposed on the intermediate matrices.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.theorem32_2`
- Dependency: [D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic](../../Combinatorics/Partitions/PartitionLInftyGeodesic.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange](InvolutionUniformExchange.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](RectangularNilpotenceBarrier.md)
