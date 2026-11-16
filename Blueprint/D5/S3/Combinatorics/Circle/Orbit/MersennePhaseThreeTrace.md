# Three-point Mersenne phase traces

## Abstract

The literal integer trace of each three-label physical phase is zero except for one positive and one negative full modulus, for every d at least three.

**Theorem 1.1 (The full physical phase filter).**

$$\forall d \in \mathrm{Nat},\; 3 \le d \Rightarrow \left(\forall j \in \operatorname{Fin}\left(d\right),\; \sum_{i\in\operatorname{Fin}\left(3 \cdot d\right),\operatorname{val}\left(i\right) \bmod d = \operatorname{val}\left(j\right)}\operatorname{actualSource}\left(3 \cdot d, \left(2^{d} - 1\right) \cdot \left(2^{d + 1} - 3\right), i\right) = \operatorname{modulus}\left(3 \cdot d\right) \cdot \left(1_{\operatorname{val}\left(j\right) = d - 3} - 1_{\operatorname{val}\left(j\right) = d - 1}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersennePhaseThreeTrace.actual_phase_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any natural d at least three and any j in Fin(d). Set B=2^d, g=B-1, q=B^2+B+1 and N=2^(3d)-1=gq. The indicator 1 with a predicate subscript is the integer one when that predicate holds and zero otherwise. The seed is the natural number (2^d-1)(2^(d+1)-3). The theorem sums SourceWidth.actualSource at every physical label i in Fin(3d) with i.val modulo d equal to j.val. The filter is exactly the three distinct original labels j, j+d and j+2d; numerical coincidences of source values never identify labels.

Put x=2^j, a=(2B-3)x, b=(5B+2)x and c=(3B+5)x, so a-b+c=0. Multiplication by B sends a to -b modulo q, and multiplication by B^2 sends a to c modulo q. The proof uses the existing SourceWidth.centered_unique, centered_bounds and centered_mod, together with explicit congruences and strict doubled bounds, to identify the centered representatives after scaling by g. It introduces no second centered uniqueness theorem.

There are four exhaustive branches. If j+4 is at most d, then 16x is at most B and the representatives modulo q are (a,-b,c), of sum zero. If j=d-3, then 8x=B and the representatives are (a,q-b,c), of sum q. If j=d-2, then 4x=B and the representatives are (a,q-b,c-q), of sum zero. If j=d-1, then 2x=B and the representatives are (a-q,2q-b,c-2q), of sum -q. Every triple satisfies the strict centered interval bounds; scaling gives the literal integer traces 0,+N,0,-N.

The only numerical premise is d at least three. The trace itself has no 19 premise, no coprimality or unit assumption, and no primality, least-period or upper-cutoff condition. In particular d=12 is included even when the arithmetic seed and modulus have an additional common factor 19. The statement remains an equality in the integers and is not replaced by congruence modulo N.

For the ongoing physical zero-algebra construction, this supplies the actual arithmetic phase values: ordinary phases contribute zero, while phases d-3 and d-1 contribute opposite full moduli. Later composition must retain the original labels and establish its own phase-union and cancellation arguments. This module proves no full subset classification, count, Boolean algebra, stabilizer theorem or infinite-family theorem. It makes no literature-novelty or full Circle claim; the supplied ordinary proof route and repository priors informed this same-family implementation.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersennePhaseThreeTrace.actual_phase_trace`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](../SourceWidth.md)
