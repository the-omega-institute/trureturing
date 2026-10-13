# Actual boundaries for Fibonacci completion

## Abstract

Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.

**Theorem 1.1 (Actual legal returns determine their canonical hull).**

$$\forall s \in Guard, U \in \operatorname{Function}\left(Bool, \operatorname{List}\left(Label\right)\right), L \in Nat,\; \left(\operatorname{lt}\left(0, L\right) \land \left(\left(\forall i \in Bool,\; \operatorname{length}\left(\operatorname{apply}\left(U, i\right)\right) = L\right) \land \left(\forall i \in Bool,\; \operatorname{LegalWord}\left(s, s, \operatorname{apply}\left(U, i\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{canonicalReturnLo}\left(U, L\right), \operatorname{canonicalReturnHi}\left(U, L\right)\right) \land \left(\left(\operatorname{notEqual}\left(\operatorname{apply}\left(U, false\right), \operatorname{apply}\left(U, true\right)\right) \Rightarrow \operatorname{lt}\left(\operatorname{canonicalReturnLo}\left(U, L\right), \operatorname{canonicalReturnHi}\left(U, L\right)\right)\right) \land \left(\left(\forall z \in Real,\; \left(\operatorname{le}\left(\operatorname{canonicalReturnLo}\left(U, L\right), z\right) \land \operatorname{le}\left(z, \operatorname{canonicalReturnHi}\left(U, L\right)\right)\right) \Rightarrow \operatorname{InSupport}\left(s, z\right)\right) \land \left(\left(\forall i \in Bool, z \in Real,\; \left(\operatorname{le}\left(\operatorname{canonicalReturnLo}\left(U, L\right), z\right) \land \operatorname{le}\left(z, \operatorname{canonicalReturnHi}\left(U, L\right)\right)\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{canonicalReturnLo}\left(U, L\right), \operatorname{compose}\left(\operatorname{apply}\left(U, i\right), z\right)\right) \land \operatorname{le}\left(\operatorname{compose}\left(\operatorname{apply}\left(U, i\right), z\right), \operatorname{canonicalReturnHi}\left(U, L\right)\right)\right)\right) \land \left(\left(\forall l \in Real, upper \in Real,\; \left(\operatorname{le}\left(l, upper\right) \land \left(\forall i \in Bool, z \in Real,\; \left(\operatorname{le}\left(l, z\right) \land \operatorname{le}\left(z, upper\right)\right) \Rightarrow \left(\operatorname{le}\left(l, \operatorname{compose}\left(\operatorname{apply}\left(U, i\right), z\right)\right) \land \operatorname{le}\left(\operatorname{compose}\left(\operatorname{apply}\left(U, i\right), z\right), upper\right)\right)\right)\right) \Rightarrow \left(\operatorname{le}\left(l, \operatorname{canonicalReturnLo}\left(U, L\right)\right) \land \operatorname{le}\left(\operatorname{canonicalReturnHi}\left(U, L\right), upper\right)\right)\right) \land \left(\left(\operatorname{canonicalReturnLo}\left(U, L\right) = \operatorname{canonicalReturnHi}\left(U, L\right) \Leftrightarrow \operatorname{apply}\left(U, false\right) = \operatorname{apply}\left(U, true\right)\right) \land \left(\operatorname{member}\left(\operatorname{canonicalReturnLo}\left(U, L\right), coefficientField\right) \land \operatorname{member}\left(\operatorname{canonicalReturnHi}\left(U, L\right), coefficientField\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/CanonicalGeometry.canonical_legal_return_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write A(i)=compose(U(i),0), a=(-g)^L, Amin=min(A(false),A(true)), and Amax=max(A(false),A(true)). The common return length L is positive. canonicalReturnLo and canonicalReturnHi use (Amin/(1-a),Amax/(1-a)) when a>0, and ((Amin+a*Amax)/(1-a^2),(Amax+a*Amin)/(1-a^2)) when a<0. The literal slope has nonzero absolute value less than one. The width is respectively (Amax-Amin)/(1-a) or (Amax-Amin)/(1+a).

Both words return legally from s to s. The displayed interval is nonempty, lies in the actual guard support, is invariant under each full return, and is contained in every nonempty invariant closed interval [l,upper]. Distinct equal-length words have distinct zero-tail scalar values: all finite suffixes at zero lie strictly inside their actual guard supports, and root branch interiors from one guard are disjoint. Induction then recovers the labels and full words from equal scalars. Literal return difference therefore gives strict hull width. The notEqual predicate in the displayed statement denotes literal inequality.

The statement permits equal words and a singleton hull. It does not identify the interval with the attractor. The singleton-hull equivalence is literal word equality. coefficientField is the intersection of all real subfields containing t, hence the original Q(t). Both computed endpoints belong to this field. The specified periodic endpoint addresses are supplied separately by canonical_periodic_endpoints.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/CanonicalGeometry.canonical_legal_return_hull`
- Dependency: [D5/S3/ConceptDynamics/Coding/DecoderOperationTrace](../DecoderOperationTrace.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry](TailGeometry.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciLiteralSource](../FibonacciLiteralSource.md)
