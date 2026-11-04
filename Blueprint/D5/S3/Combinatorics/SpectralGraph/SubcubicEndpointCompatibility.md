# Rational symmetric endpoint compatibility

## Abstract

Complete rational symmetric endpoint compatibility for an actual finite rooted subcubic tree.

Fix an actual nonempty finite connected simple tree G, an actual selected vertex o, a rational shift a and a strictly positive rational link c. Its matrix is T = a Id + c Adj(G), with unit zero-diagonal adjacency in the original coordinates. Write h_j for chainNorm(T,o,a,c,j), using the fixed Chebyshev recurrence described in TreeEndpointMomentCertificates. The shift can be zero or negative; T need not be positive, contractive or cyclic.

**Definition 1.1 (Exact finite moment agreement).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, \operatorname{Rat}\right),\; \forall o \in V,\; \forall n \in \operatorname{Nat},\; \forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \operatorname{Rat}\right),\; \forall d \in \operatorname{Nat},\; \operatorname{MatchesThrough}\left(M, o, J, d\right) \Leftrightarrow \left(\forall k \in \operatorname{Nat},\; k \le d \Rightarrow \left(M^{k}\right)\left(o, o\right) = \left(J^{k}\right)\left(0, 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.MatchesThrough` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This compares moments at the actual port with moments at coordinate zero. The upper index is inclusive. Every nonempty finite competitor order occurs uniquely as n+1; there is no hidden size bound.

**Definition 1.2 (All moments and every order).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, \operatorname{Rat}\right),\; \forall o \in V,\; \operatorname{Compatible}\left(M, o\right) \Leftrightarrow \left(\exists n \in \operatorname{Nat},\; \exists J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \operatorname{Rat}\right),\; \operatorname{PositiveJacobi}\left(J\right) \land \left(\forall k \in \operatorname{Nat},\; \left(M^{k}\right)\left(o, o\right) = \left(J^{k}\right)\left(0, 0\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A competitor has rational coefficients, symmetry, tridiagonality and strictly positive existing adjacent links. It must match every natural moment, including the zeroth moment. The link list is empty in order one.

**Definition 1.3 (The actual uniform path matrix).**

$$\forall n \in \operatorname{Nat},\; \forall a \in \operatorname{Rat},\; \forall c \in \operatorname{Rat},\; \operatorname{pathMatrix}\left(n, a, c\right) = \operatorname{uniformMatrix}\left(\operatorname{pathGraph}\left(n\right), a, c\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.pathMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The argument n is the order itself. In contrast, existential competitor parameters use n+1 so that no empty competitor is admitted.

**Theorem 1.4 (The complete endpoint criterion and both finite certificates).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsTree}\left(G\right) \Rightarrow \left(\left(\forall x \in V,\; \operatorname{degree}\left(G, x\right) \le 3\right) \Rightarrow \left(\forall o \in V,\; \forall a \in \operatorname{Rat},\; \forall c \in \operatorname{Rat},\; 0 < c \Rightarrow \left(\exists r \in \operatorname{Nat},\; 0 < r \land \left(r \le \operatorname{card}\left(V\right) \land \left(\left(\forall j \in \operatorname{Nat},\; j < r \Rightarrow \operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, j\right) = 1\right) \land \left(\operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, r\right) \ne 1 \land \left(\left(\operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, r\right) = 0 \Leftrightarrow \operatorname{EndpointPath}\left(G, o\right)\right) \land \left(\left(\operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, r\right) = 0 \lor \left(\operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, r\right) = 2 \lor \operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, r\right) = 3\right)\right) \land \left(\left(\operatorname{Compatible}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o\right) \Leftrightarrow \operatorname{EndpointPath}\left(G, o\right)\right) \land \left(\left(\left(\neg \operatorname{EndpointPath}\left(G, o\right)\right) \Rightarrow \left(\forall n \in \operatorname{Nat},\; \forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \operatorname{Rat}\right),\; \operatorname{PositiveJacobi}\left(J\right) \Rightarrow \left(\neg \operatorname{MatchesThrough}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, J, 2 \cdot r\right)\right)\right)\right) \land \left(\operatorname{EndpointPath}\left(G, o\right) \Rightarrow \left(r = \operatorname{card}\left(V\right) \land \left(\left(\exists e \in \operatorname{GraphIso}\left(G, \operatorname{pathGraph}\left(r\right)\right),\; e\left(o\right) = 0 \land \left(\operatorname{reindex}\left(\operatorname{uniformMatrix}\left(G, a, c\right), e, e\right) = \operatorname{pathMatrix}\left(r, a, c\right) \land \left(\operatorname{transport}\left(e, \operatorname{unit}\left(o\right)\right) = \operatorname{unit}\left(0\right) \land \left(\left(\forall f \in V \to \operatorname{Rat},\; \operatorname{mulVec}\left(\operatorname{pathMatrix}\left(r, a, c\right), \operatorname{transport}\left(e, f\right)\right) = \operatorname{transport}\left(e, \operatorname{mulVec}\left(\operatorname{uniformMatrix}\left(G, a, c\right), f\right)\right)\right) \land \left(\forall k \in \operatorname{Nat},\; \left(\operatorname{uniformMatrix}\left(G, a, c\right)^{k}\right)\left(o, o\right) = \left(\operatorname{pathMatrix}\left(r, a, c\right)^{k}\right)\left(0, 0\right)\right)\right)\right)\right)\right) \land \left(\forall n \in \operatorname{Nat},\; \forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{Fin}\left(n + 1\right), \operatorname{Rat}\right),\; \operatorname{PositiveJacobi}\left(J\right) \Rightarrow \left(\operatorname{MatchesThrough}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, J, 2 \cdot r\right) \Rightarrow \left(n + 1 = r \land J = \operatorname{pathMatrix}\left(n + 1, a, c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.complete78_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a first positive r with h_r different from one: all earlier nonnegative indices have norm one, and 1 <= r <= the actual number of vertices. Its value is zero, two or three, and zero is equivalent to G being a path with o at an endpoint. EndpointPath means a genuine rooted graph isomorphism to a nonempty path, so the singleton is included and a nontrivial path's interior port is excluded. Compatibility with a rational symmetric positive-link endpoint matrix is equivalent to precisely that same actual geometric condition. If it fails, moments zero through 2r exclude every such competitor of every finite order. If it holds, r equals the actual order, and the same finite prefix forces every matching competitor to have that order, every diagonal a, and every link c: its entire matrix is pathMatrix. The theorem also constructs an actual graph isomorphism e sending o to zero. In the display, transport(e,f) means f composed with the inverse coordinate equivalence. It sends the actual selected unit vector to the first path unit vector and intertwines T with the path matrix on every vector; reindexing both matrix coordinates gives exactly that path matrix. Consequently every moment agrees, not merely the finite certificate.

The proof earns a maximal simple saturated rooted stem in the actual tree. Its fixed recurrence vectors are distinct actual unit coordinates until its terminal forward boundary, whose size is zero, two or three. Generic positive Jacobi rigidity forces any matching competitor to expose the same initial coordinates and coefficients. A shorter competitor contradicts a required unit norm; an exact terminating competitor has next norm zero; a larger competitor has next norm equal to the square of its next link divided by c. For a nonzero boundary, the exact rational-square theorem and primality of two and three exclude a rational competitor. For a zero boundary, connectedness exhausts the actual graph and a coordinate isomorphism produces the positive solution. Positive next links prohibit a larger order, and symmetry plus the band condition identify every matrix entry.

This is an algebraic classification. It supplies no installed scalar service, rights, preparation, reset implementation, paid backing or physical cost bound. The distinct installed-service consumer and its execution or horizon conditions are outside this theorem. No geometry oracle, other port or external advice is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.Compatible`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.MatchesThrough`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.complete78_3`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.pathMatrix`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates](TreeEndpointMomentCertificates.md)
