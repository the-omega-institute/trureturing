# Joint ordered-colouring Gram matrices

## Abstract

Joint ordered-colouring Gram matrices

Fix an arbitrary natural degree n. An ordered colouring is a map f from Fin n to Fin 3. Its three labelled fibres are the three ordered blocks. For an integer margin a, Colourings(n,a) consists of f with cardinality of the i-th fibre equal to a(i) in the integers. The symmetric group acts by precomposition with the inverse permutation. A negative margin gives the empty type. Zero margins remain labelled empty blocks, and equal margins retain distinct labels: there is no extra factorial for repeated or empty rows.

eta(a,g) is the number of colourings fixed by g, with margin a. colouringRepresentation is the actual complex permutation representation on Colourings(n,a), defined independently of eta. The character formula below proves that its trace is eta. Fixedness under g inverse and fixedness under g are equivalent.

A contingency table is a function A from Fin 3 times Fin 3 to the natural numbers, with total n and integer row and column margins a and b. contingencyTables is the finite set of such functions and C(n,a,b) is its cardinality. Each entry is automatically at most n. This definition also gives zero if a margin is negative or has the wrong total.

For each single permutation g, a pair of invariant colourings f and h is equivalent to the invariant joint colouring x mapped to (f(x),h(x)). The joint fibre A(i,j) has the intersection cardinality of the two blocks. Its row and column sums recover the original marginal sizes. Summing first over g and then over joint colourings counts each joint colouring with the order of its fibre-preserving subgroup. Grouping by its nine fibre sizes gives n factorial for each table: all colourings of the same fibre sizes form one orbit, every such fibre-size function occurs, and quotient cardinality times stabilizer cardinality is the order of the symmetric group. Both marginal invariance conditions use the same g throughout.

For a natural triple r and a permutation s of Fin 3, shifted(r,s)(i) is the integer r(i)-i+s(i). Define Theta(r,g) as the sum of sign(s) times eta(shifted(r,s),g) over all six s. The signed contingency Gram is the double sum of sign(s)sign(t) C(n,shifted(r,s),shifted(q,t)). Expanding both finite sums and applying the joint Gram formula proves the signed character identity below. This uses no Specht multiplicity, tableau number or Frobenius coefficient.

**Theorem 1.1 (The count is the actual permutation trace).**

$$\forall n \in \operatorname{Nat},\; \forall a \in \operatorname{IntTriple},\; \forall g \in \operatorname{PermFin}\left(n\right),\; \operatorname{traceColouring}\left(n, a, g\right) = \operatorname{complexNatCast}\left(\operatorname{eta}\left(a, g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.character_colouringRepresentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

traceColouring is the character of colouringRepresentation; eta is fixedColourings. The trace is obtained from the actual permutation action.

**Theorem 1.2 (Joint fixed colourings give the contingency Gram matrix).**

$$\forall n \in \operatorname{Nat},\; \forall a \in \operatorname{IntTriple},\; \forall b \in \operatorname{IntTriple},\; \operatorname{sumPerm}\left(n, \operatorname{etaProduct}\left(a, b\right)\right) = \operatorname{mul}\left(\operatorname{factorial}\left(n\right), \operatorname{C}\left(n, a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_fixedColourings_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

etaProduct(a,b)(g) is eta(a,g)eta(b,g). C counts the finite tables just defined. The equation is unnormalised and valid for arbitrary integer margins.

**Theorem 1.3 (The Gram identity for actual complex permutation traces).**

$$\forall n \in \operatorname{Nat},\; \forall a \in \operatorname{IntTriple},\; \forall b \in \operatorname{IntTriple},\; \operatorname{sumPerm}\left(n, \operatorname{colouringTraceProduct}\left(a, b\right)\right) = \operatorname{complexNatCast}\left(\operatorname{mul}\left(\operatorname{factorial}\left(n\right), \operatorname{C}\left(n, a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_colouringTrace_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Both factors are the actual characters of the ordered-colouring representations. The formula is obtained by the exact natural-to-complex cast of the joint count.

**Theorem 1.4 (The signed contingency sum is the virtual character Gram matrix).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall q \in \operatorname{NatTriple},\; \operatorname{sumPerm}\left(n, \operatorname{ThetaProduct}\left(r, q\right)\right) = \operatorname{mul}\left(\operatorname{intNatCast}\left(\operatorname{factorial}\left(n\right)\right), \operatorname{signedContingencyGram}\left(n, r, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_virtualCharacter_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

ThetaProduct(r,q)(g) is Theta(r,g)Theta(q,g). The finite double sum has six times six terms, but the symmetric-group degree n is unrestricted.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.character_colouringRepresentation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_colouringTrace_mul`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_fixedColourings_mul`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowGram.sum_virtualCharacter_mul`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtYoungTrace](SpechtYoungTrace.md)
