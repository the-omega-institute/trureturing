# Combining invariant product blocks

## Abstract

An equivariant product decomposition combines independent ordered commutator-value coverage on its invariant blocks with the same exponent and exact tuple length.

**Theorem 1.1 (Ordered value sets combine under an equivariant splitting).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/InvariantBlockReduction.prescribed_coverage_of_equivariant_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/InvariantBlockReduction.prescribed_coverage_of_equivariant_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any group, let S(r) be a family of groups indexed by an arbitrary type, and fix natural q and m. Let k be a tuple of automorphisms of A and l(r) a tuple of automorphisms of S(r), each indexed by Fin m. Assume a group isomorphism e from A to the full dependent product of S(r), equivariant in the exact sense e(k(i)(x))(r) = l(r)(i)(e(x)(r)) for every i, x and r. If PrescribedCommutatorCoverage(S(r),q,m,l(r)) holds for every r, then PrescribedCommutatorCoverage(A,q,m,k) holds. No finiteness assumption on A, the index type or the factors is required.

Choose all block inner corrections before any target and use e inverse to form one tuple in A. For a target t, choose each block commutator tuple for e(t)(r) and combine these using e inverse. Equivariance intertwines the corrected automorphisms and every natural power of them; evaluation maps preserve the ordered products. Injectivity of e then proves equality with t. The same q and m are used in every block and in A.

The reduction follows the invariant-block step on printed pages 227–228 of Nikolov and Segal, On finitely generated profinite groups, I, DOI 10.4007/annals.2007.165.171. The isomorphism and its equivariance are explicit hypotheses. This theorem does not construct the actual factor-orbit splitting or prove the transitive Proposition 10.2 input. Applied to the corrected action on a normal subgroup, it supplies the value-set premise for the conditional prescribed coset-power theorem; uniform width and strong completeness remain unproved.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/InvariantBlockReduction.prescribed_coverage_of_equivariant_product`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge](CosetPowerBridge.md)
