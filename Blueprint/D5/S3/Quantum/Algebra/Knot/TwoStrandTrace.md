# Exact Trace of Signed Two-Strand Braids

## Abstract

Every signed power of the two-strand Artin generator has an exact weighted path-trace value.

**Theorem 1.1 (All integer crossing exponents).**

$$\begin{gathered}\operatorname{FiniteSymmetricPositivePerronData}\left(L, R, d, delta\right); \operatorname{Nonzero}\left(A\right); delta = -\operatorname{Pow}\left(A, 2\right)-\operatorname{Pow}\left(\operatorname{Inv}\left(A\right), 2\right)\\\forall s \in L,\; \forall m \in Z,\; \operatorname{F}\left(\operatorname{twoStrand}\left(m\right)\right) = delta\,\operatorname{Pow}\left(-\operatorname{Pow}\left(A, 3\right), m\right)\,(\operatorname{Pow}\left(\operatorname{Inv}\left(A\right), m\right)\,(1-\operatorname{Pow}\left(\operatorname{Inv}\left(delta\right), 2\right))+\operatorname{Pow}\left(-\operatorname{Pow}\left(A, 3\right), m\right)\,\operatorname{Pow}\left(\operatorname{Inv}\left(delta\right), 2\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/TwoStrandTrace.two_strand_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be any finite decidable vertex type, R a decidable symmetric relation, d strictly positive real weights, and delta strictly positive with the exact Perron equality at every vertex. Fix any start s and nonzero complex A satisfying delta = -A squared minus A inverse squared. twoStrand(m) is the m-th integer power of the sole generator in the repository's actual two-strand Artin presentation. Empty endpoint fibers are retained. The theorem applies to every integer m, including zero and negative values.

Write P for the existing lastProjection on the two-edge path space. The actual represented generator is A inverse times (1-P) plus -A cubed times P. Its inverse has the reciprocal two coefficients. Idempotence gives two orthogonal algebraic sectors P and 1-P, so their coefficients multiply independently. Integer induction through the actual unit and its inverse yields the signed-power formula. No diagonalization, nonempty matrix block or extra matrix-inverse assumption is used.

The existing Perron Markov law gives tau(P) = delta inverse squared and tau(1) = 1. Combining these with the two-sector formula and the exact integer writhe m proves the displayed value. This supplies a concrete evaluation interface downstream of the existing representation and Markov descent. It computes every two-strand torus word and its mirror directly from scalar powers.

The mathematics is classical Temperley-Lieb and Jones theory. The crossing and writhe convention is the one already fixed by WeightedPathArtinRepresentation and its Aharonov-Jones-Landau source record, Library/Topology/aharonovjoneslandau2005jones.md. The result evaluates the formal algebraic Markov invariant. A geometric closure map and convention-preserving Jones identification remain separate obligations. This theorem does not construct the Aiello-Baader-Ferretti modulo-three witness or solve their Question 1.

The four-slot audit is unfinished. Its Reg mirror carries compiled actual-law, variation, sensitivity and dependence proofs, but the current source binding reports IE-C050 source.dictionary_or_proof_coordinate. The exact original theorem telescope and failed binding evidence are tracked in https://github.com/the-omega-institute/trureturing/issues/16285. This is an unresolved registration, not a validated source correspondence.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/TwoStrandTrace.two_strand_trace`
- Dependency: [D5/S3/Quantum/Algebra/Knot/WeightedPathArtinRepresentation](WeightedPathArtinRepresentation.md)
