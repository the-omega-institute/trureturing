# Native Tree Obstruction for Polynomial Trace Families

## Abstract

Separated-atom finite families cannot give exact alpha replies on all native trees and addresses.

Source is the original carrier of all finite Boolean-labelled binary trees, including a single leaf. Address is List Bool, with false for left and true for right. The original readout has four replies: alpha for a true leaf, beta for a false leaf, branch for an internal node, and absent for a missing address. All queries here are at epoch zero.

**Theorem 1.1 (Finite chart and descriptor families cannot be exact everywhere).**

$$\operatorname{Growth}\left(f, C, s\right) \land sourceCover \land addressCover \land allRealizationExactness \Rightarrow False$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePolynomialDescriptorObstruction.growth_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K,T be finite, with arbitrary dependent carriers X(k),Y(t). A predicate D(k,x) specifies which source-chart points are used. The maps Theta(k,x) cover every original finite tree using points satisfying D. Real(t,y,a) relates a descriptor to each of its physical address realizations, and every finite address has a descriptor. For every k,t,x,y,a with D(k,x) and Real(t,y,a), require f(k,t,x,y)=true exactly when readout(a,Theta(k,x))=alpha. No definability or injectivity of Theta, D, or Real is assumed. Each component f(k,t) has a supplied Growth derivation.

The complete shape fullPattern(d) recursively pairs two complete shapes, starting with one hole at depth zero. Its frontier has 2^d positions. Choose n with C_total*(n+1)^s_total<2^n and embed Fin n into the frontier at depth n. Its actual frontier addresses are distinct and all have length n. Choose covering descriptors for those actual addresses before choosing any Boolean pattern or source tree. Each chosen address itself satisfies Real for its chosen descriptor.

For any Boolean vector b on Fin n, extend the assignment of leaves of label b(i) from the embedded positions to the whole frontier, using beta elsewhere. Filling that frontier gives one actual finite tree. NativeDepthPatterns.frontier_geometry recovers all its assigned subtrees simultaneously. The original address geometry turns these subtrees into alpha or beta replies. Source coverage supplies one chart point for the whole tree; exactness at the fixed actual address realizations transfers b to a trace of the joint relation. Thus all 2^n Boolean vectors occur, in contradiction with the finite-family polynomial upper bound.

The obstruction assumes Growth certificates. It establishes no claim that arbitrary quantified Presburger formulas supply these certificates, and gives no undecidability or controller result. The predicates D and Real may be arbitrary. Exactness at only one chosen address per descriptor would not meet the hypotheses; exactness applies at every related physical address.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePolynomialDescriptorObstruction.growth_obstruction`
- Dependency: [D5/S0/Computability/PresburgerFiniteFamilies](../../../../S0/Computability/PresburgerFiniteFamilies.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
