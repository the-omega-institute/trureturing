# Actual boundaries for Fibonacci completion

## Abstract

Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.

**Theorem 1.1 (Every supported scalar has one legal itinerary).**

$$\forall s \in Guard, z \in Real,\; \operatorname{InSupport}\left(s, z\right) \Rightarrow \left(\exists a \in \operatorname{Function}\left(Nat, Label\right), x \in \operatorname{Function}\left(Nat, Real\right), path \in \operatorname{Function}\left(Nat, Guard\right),\; \left(\operatorname{apply}\left(path, 0\right) = s \land \left(\left(\forall p \in Nat,\; \operatorname{nextGuard}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(a, p\right)\right) = \operatorname{some}\left(\operatorname{apply}\left(path, \operatorname{add}\left(p, 1\right)\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{InSupport}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(x, p\right)\right)\right) \land \left(\forall p \in Nat,\; \operatorname{apply}\left(x, p\right) = \operatorname{branch}\left(\operatorname{apply}\left(a, p\right), \operatorname{apply}\left(x, \operatorname{add}\left(p, 1\right)\right)\right)\right)\right)\right)\right) \land \operatorname{apply}\left(x, 0\right) = z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.lawful_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed branch images cover [-1,phi] at G0 and [-1,t] at G1. The inverse branch (shift(label)-z)/g remains in its next guard support. Iterating supported guard-scalar pairs gives one label sequence, one coordinate sequence and one legal guard path with the requested scalar. Shared branch endpoints remain legal.

**Theorem 1.2 (Finite legal zero tails approximate every supported scalar).**

$$\forall s \in Guard, z \in Real, epsilon \in Real,\; \left(\operatorname{InSupport}\left(s, z\right) \land \operatorname{lt}\left(0, epsilon\right)\right) \Rightarrow \left(\exists e \in Guard, w \in \operatorname{List}\left(Label\right),\; \operatorname{LegalWord}\left(s, e, w\right) \land \operatorname{lt}\left(\operatorname{abs}\left(\operatorname{subtract}\left(z, \operatorname{coordinate}\left(w, 0\right)\right)\right), epsilon\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.finite_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Truncate the same itinerary after n labels. The exact remaining-coordinate error is (-g)^n*x(n), whose absolute value is at most phi*g^n. Geometric convergence gives every positive tolerance. This density concerns the full guard support; it does not identify that interval with a two-return attractor.

**Theorem 1.3 (A finite tail in a supported interval interior).**

$$\forall s \in Guard, lo \in Real, hi \in Real,\; \left(\operatorname{lt}\left(lo, hi\right) \land \left(\forall z \in Real,\; \left(\operatorname{le}\left(lo, z\right) \land \operatorname{le}\left(z, hi\right)\right) \Rightarrow \operatorname{InSupport}\left(s, z\right)\right)\right) \Rightarrow \left(\exists e \in Guard, w \in \operatorname{List}\left(Label\right),\; \operatorname{LegalWord}\left(s, e, w\right) \land \left(\operatorname{lt}\left(lo, \operatorname{coordinate}\left(w, 0\right)\right) \land \left(\operatorname{lt}\left(\operatorname{coordinate}\left(w, 0\right), hi\right) \land \left(\operatorname{OperationFiniteSource}\left(\operatorname{address}\left(w\right)\right) \land \left(\exists path \in \operatorname{Function}\left(Nat, Guard\right),\; \operatorname{apply}\left(path, 0\right) = s \land \left(\left(\forall p \in Nat,\; \operatorname{nextGuard}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(\operatorname{address}\left(w\right), p\right)\right) = \operatorname{some}\left(\operatorname{apply}\left(path, \operatorname{add}\left(p, 1\right)\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{InSupport}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(\operatorname{coordinateSequence}\left(w\right), p\right)\right)\right) \land \left(\forall p \in Nat,\; \operatorname{apply}\left(\operatorname{coordinateSequence}\left(w\right), p\right) = \operatorname{branch}\left(\operatorname{apply}\left(\operatorname{address}\left(w\right), p\right), \operatorname{apply}\left(\operatorname{coordinateSequence}\left(w\right), \operatorname{add}\left(p, 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.finite_tail_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A midpoint approximation within half the interval width yields a finite legal word whose zero-tail scalar lies strictly between lo and hi. coordinateSequence(w)(p)=coordinate(w,p). The full eventually-L0 address and its entire legal supported coordinate path are retained, for either initial guard.

**Theorem 1.4 (Splicing one fixed legal coordinate tail).**

$$\forall s \in Guard, e \in Guard, w \in \operatorname{List}\left(Label\right), a \in \operatorname{Function}\left(Nat, Label\right), x \in \operatorname{Function}\left(Nat, Real\right), path \in \operatorname{Function}\left(Nat, Guard\right),\; \left(\operatorname{LegalWord}\left(s, e, w\right) \land \left(\operatorname{apply}\left(path, 0\right) = e \land \left(\left(\forall p \in Nat,\; \operatorname{nextGuard}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(a, p\right)\right) = \operatorname{some}\left(\operatorname{apply}\left(path, \operatorname{add}\left(p, 1\right)\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{InSupport}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(x, p\right)\right)\right) \land \left(\forall p \in Nat,\; \operatorname{apply}\left(x, p\right) = \operatorname{branch}\left(\operatorname{apply}\left(a, p\right), \operatorname{apply}\left(x, \operatorname{add}\left(p, 1\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists beta \in \operatorname{Function}\left(Nat, Label\right), X \in \operatorname{Function}\left(Nat, Real\right), q \in \operatorname{Function}\left(Nat, Guard\right),\; \left(\operatorname{apply}\left(q, 0\right) = s \land \left(\left(\forall p \in Nat,\; \operatorname{nextGuard}\left(\operatorname{apply}\left(q, p\right), \operatorname{apply}\left(beta, p\right)\right) = \operatorname{some}\left(\operatorname{apply}\left(q, \operatorname{add}\left(p, 1\right)\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{InSupport}\left(\operatorname{apply}\left(q, p\right), \operatorname{apply}\left(X, p\right)\right)\right) \land \left(\forall p \in Nat,\; \operatorname{apply}\left(X, p\right) = \operatorname{branch}\left(\operatorname{apply}\left(beta, p\right), \operatorname{apply}\left(X, \operatorname{add}\left(p, 1\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{apply}\left(X, 0\right) = \operatorname{compose}\left(w, \operatorname{apply}\left(x, 0\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{lt}\left(p, \operatorname{length}\left(w\right)\right) \Rightarrow \operatorname{apply}\left(beta, p\right) = \operatorname{getElem}\left(w, p\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{apply}\left(beta, \operatorname{add}\left(\operatorname{length}\left(w\right), p\right)\right) = \operatorname{apply}\left(a, p\right)\right) \land \left(\forall p \in Nat,\; \operatorname{apply}\left(X, \operatorname{add}\left(\operatorname{length}\left(w\right), p\right)\right) = \operatorname{apply}\left(x, p\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.prepend_legal_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TailPath(s,a,x,path) means that path starts at s, every label follows nextGuard, every scalar lies in its corresponding support, and every affine recurrence holds. A legal finite prefix prepends exactly its labels and composition value. Both shifted futures are exact, including the recurrence at the splice boundary.

**Theorem 1.5 (Exact color cells and all five endpoint flags).**

$$\forall o \in Ownership, c \in Color, z \in Real,\; \operatorname{Cell}\left(o, c, z\right) \Leftrightarrow \operatorname{FlagInterval}\left(\operatorname{cut}\left(\operatorname{val}\left(c\right)\right), \operatorname{cut}\left(\operatorname{add}\left(\operatorname{val}\left(c\right), 1\right)\right), \operatorname{lowerOwned}\left(o, c\right), \operatorname{upperOwned}\left(o, c\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.cell_flag_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FlagInterval(lo,hi,left,right,z) is lo<=z<=hi with z=lo implying left and z=hi implying right. lowerOwned is true at color zero and otherwise uses the corresponding true flag; upperOwned is true at color five and otherwise uses the corresponding false flag. These are exactly the original Cell boundaries.

**Theorem 1.6 (Closed error dilation with actual endpoint ownership).**

$$\forall o \in Ownership, theta \in Real, c \in Color, z \in Real,\; \operatorname{le}\left(0, theta\right) \Rightarrow \left(\operatorname{OwnedColor}\left(o, theta, c, z\right) \Leftrightarrow \left(\operatorname{InSupport}\left(G0, z\right) \land \operatorname{FlagInterval}\left(\operatorname{subtract}\left(\operatorname{cut}\left(\operatorname{val}\left(c\right)\right), theta\right), \operatorname{add}\left(\operatorname{cut}\left(\operatorname{add}\left(\operatorname{val}\left(c\right), 1\right)\right), theta\right), \operatorname{lowerOwned}\left(o, c\right), \operatorname{upperOwned}\left(o, c\right), z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.owned_color_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OwnedColor(o,theta,c,z) requires z in G0 support and a target u in the actual Cell(o,c) with abs(z-u)<=theta. Dilation shifts the two cell endpoints by theta and retains their original ownership. Support is intersected separately, so clipping an expanded interval does not transfer an unrelated ownership flag to a new boundary. At theta zero the target is z itself.

**Theorem 1.7 (Attainable colors are exact observe error outcomes).**

$$\forall o \in Ownership, theta \in Real, c \in Color, z \in Real,\; \operatorname{InSupport}\left(G0, z\right) \Rightarrow \left(\operatorname{OwnedColor}\left(o, theta, c, z\right) \Leftrightarrow \left(\exists error \in Real,\; \operatorname{le}\left(\operatorname{abs}\left(error\right), theta\right) \land \operatorname{observe}\left(o, z, error\right) = c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.owned_color_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For supported z, clipping z+error changes its distance from z by at most abs(error). Conversely a supported target u is fixed by clip and is obtained with error=u-z. This proves both directions of the actual observe relation, including every ownership flag.

**Theorem 1.8 (Actual attainable color sets are intervals).**

$$\forall o \in Ownership, theta \in Real, c \in Color,\; \operatorname{le}\left(0, theta\right) \Rightarrow \operatorname{OrdConnected}\left(\operatorname{setOfOwnedColor}\left(o, theta, c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.owned_color_ordConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

setOfOwnedColor(o,theta,c) is the set of real z satisfying OwnedColor(o,theta,c,z). Its supported flagged interval is order-connected, including empty sets and excluded endpoints.

**Theorem 1.9 (The actual competing-tail intersection is an interval).**

$$\forall o \in Ownership, theta \in Real, s \in Guard, Q \in \operatorname{List}\left(Label\right), V \in \operatorname{List}\left(Label\right), h \in \operatorname{List}\left(Color\right), W \in \operatorname{Function}\left(Bool, \operatorname{List}\left(Color\right)\right), z \in Real,\; \operatorname{le}\left(0, theta\right) \Rightarrow \operatorname{OrdConnected}\left(\operatorname{CompetingT}\left(o, theta, s, Q, V, h, W\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.competingT_ordConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CompetingT is the intersection of the terminal guard support, every actual Q-suffix color constraint for r<h.length, and every V-suffix constraint for each of the two W words. Affine preimages preserve order-connectedness for either slope sign. No terminal color test is added.

**Theorem 1.10 (Concrete tail membership and actual slot errors).**

$$\forall o \in Ownership, theta \in Real, s \in Guard, Q \in \operatorname{List}\left(Label\right), V \in \operatorname{List}\left(Label\right), h \in \operatorname{List}\left(Color\right), W \in \operatorname{Function}\left(Bool, \operatorname{List}\left(Color\right)\right), z \in Real,\; \left(\operatorname{LegalWord}\left(G0, s, Q\right) \land \operatorname{LegalWord}\left(s, s, V\right)\right) \Rightarrow \left(\operatorname{member}\left(z, \operatorname{CompetingT}\left(o, theta, s, Q, V, h, W\right)\right) \Leftrightarrow \left(\operatorname{InSupport}\left(s, z\right) \land \left(\operatorname{BlockSupply}\left(o, theta, false, Q, h, z\right) \land \left(\forall i \in Bool,\; \operatorname{BlockSupply}\left(o, theta, false, V, \operatorname{apply}\left(W, i\right), z\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.competingT_mem_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Legal Q and V words transport support through every suffix. Membership in CompetingT is exactly supported terminal membership and the closed BlockSupply conditions for the stem and both return-color choices.

**Theorem 1.11 (Finite endpoint costs supply every interior slot).**

$$\forall o \in Ownership, theta \in Real, lo \in Real, hi \in Real, w \in \operatorname{List}\left(Label\right), cs \in \operatorname{List}\left(Color\right), x \in Real,\; \left(\operatorname{le}\left(0, theta\right) \land \left(\operatorname{EndpointCertificate}\left(theta, lo, hi, w, cs\right) \land \left(\operatorname{lt}\left(lo, x\right) \land \operatorname{lt}\left(x, hi\right)\right)\right)\right) \Rightarrow \operatorname{BlockSupply}\left(o, theta, false, w, cs, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.certificate_actual_slots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

EndpointCertificate gives supported images of lo and hi at each departure suffix and bounds max(cut(c)-z,0,z-cut(c+1)) by theta at each image. A nonzero literal suffix slope sends an interior scalar strictly between those two endpoint images. This yields actual ownership-sensitive error witnesses at theta, including theta zero.

**Theorem 1.12 (Endpoint-sensitive scalar competing-tail orbits).**

$$\forall T \in \operatorname{Set}\left(Real\right), a \in Real, y \in Real,\; \left(\operatorname{OrdConnected}\left(T\right) \land \left(\operatorname{lt}\left(\operatorname{negate}\left(1\right), a\right) \land \left(\operatorname{lt}\left(a, 1\right) \land \operatorname{notEqual}\left(a, 0\right)\right)\right)\right) \Rightarrow \left(\left(\forall x \in Real,\; \left(\forall n \in Nat,\; \operatorname{member}\left(\operatorname{iterateApply}\left(\operatorname{CenteredAffine}\left(y, a\right), n, x\right), T\right)\right) \Leftrightarrow \operatorname{ifThenElse}\left(\operatorname{lt}\left(0, a\right), \operatorname{member}\left(x, T\right) \land \operatorname{member}\left(y, \operatorname{closure}\left(T\right)\right), \operatorname{member}\left(x, T\right) \land \operatorname{member}\left(\operatorname{apply}\left(\operatorname{CenteredAffine}\left(y, a\right), x\right), T\right)\right)\right) \land \left(\left(\exists x \in Real,\; \forall n \in Nat,\; \operatorname{member}\left(\operatorname{iterateApply}\left(\operatorname{CenteredAffine}\left(y, a\right), n, x\right), T\right)\right) \Leftrightarrow \operatorname{ifThenElse}\left(\operatorname{lt}\left(0, a\right), \operatorname{Nonempty}\left(T\right) \land \operatorname{member}\left(y, \operatorname{closure}\left(T\right)\right), \operatorname{member}\left(y, T\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.competing_tail_orbit_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CenteredAffine(y,a)(x)=y+a(x-y), and iterateApply(f,n,x)=f^[n](x). T is any order-connected real set, including empty and singleton intervals. For 0<a<1 the full orbit condition is x in T and y in closure(T); membership of y itself is unnecessary. For -1<a<0 it is x in T and f(x) in T; these two actual members also force y in T, and this is equivalent to a nonempty feasible orbit set. Positive iterates converge to y and lie strictly between the initial point and y; negative iterates remain in the closed segment between x and f(x). Actual open and closed endpoint membership is retained.

This is the scalar interval part of the original39.5 criterion. The concrete owned-color intersection and fixed-tail constructions connect this scalar condition to actual legal source records under their explicit hull and return-map data. An optional original-piece restriction requires a member of the feasible orbit set in that piece and is imposed only when present in the family. Canonical hull nondegeneracy, singleton-return reduction, canonical budget necessity and optional whole-prefix piece conditions remain separate original obligations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.cell_flag_interval`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.certificate_actual_slots`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.competingT_mem_actual`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.competingT_ordConnected`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.competing_tail_orbit_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.finite_approximation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.finite_tail_interior`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.lawful_tail`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.owned_color_error`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.owned_color_interval`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.owned_color_ordConnected`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry.prepend_legal_tail`
- Dependency: [D5/S3/ConceptDynamics/Coding/DecoderOperationTrace](../DecoderOperationTrace.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Operations](Operations.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciLiteralSource](../FibonacciLiteralSource.md)
