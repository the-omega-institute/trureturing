# Compact convex zero fibers and one common confirmer

## Abstract

Compact convex zero fibers and one common confirmer.

Work on the original finite-dimensional real carrier with a closed pointed generating cone C, a unit u strictly positive on nonzero cone points, the full normalized base K, every native pure point p, and the full original proper-effect interval. For each p, zeroFiber C u p contains exactly the x in K for which some proper confirmer of p vanishes at x.

**Theorem 1.1 (Zero gluing gives compact convex fibers and one common confirmer).**

Lean statement: `D5/S3/Quantum/Foundation/ZeroGluingCommonWitness.zeroFiber_compact_convex_common_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ZeroGluingCommonWitness.zeroFiber_compact_convex_common_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native pure p, the full-base zero fiber is compact and convex. The proof projects the compact relation of confirming effects and normalized states, then uses original zeroGluing for midpoint closure and closed dyadic approximation for arbitrary real convex combinations.

If the zero fiber is nonempty, one original proper confirmer f confirms p and has {x in K | f(x)=0} equal to the entire zero fiber. A relative interior point and a small affine extrapolation force f to vanish at every fiber point by proper nonnegativity. The empty fiber is retained by the implication without selecting an interior point. No finite-pure, reciprocity, least-confirmation, or additional hypothesis is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ZeroGluingCommonWitness.zeroFiber_compact_convex_common_witness`
- Dependency: [D5/S3/Quantum/Foundation/WeightedRelationConfirmation](WeightedRelationConfirmation.md)
