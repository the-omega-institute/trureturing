# Actual Finite Rectangle Transport

## Abstract

Every finite rectangle menu on the positive five-mode fiber has an exact continuous transport realization.

**Theorem 1.1 (Exact realization by finite continuous controls).**

$$\begin{gathered}\forall b: \operatorname{Base}, \operatorname{ValidBase}\left(b\right)\Rightarrow\\{}\forall k_{0}\in \operatorname{J}\left(b\right), \forall A:\operatorname{List}\left(\mathbb{R}^{2}\right),\\{}(\forall e\in A, \operatorname{fst}\left(e\right)\in \operatorname{J}\left(b\right))\Rightarrow\\{}\exists q:\mathbb{R}\to \operatorname{State}, \operatorname{Admissible}\left(b, \operatorname{Duration}\left(A\right), q\right)\land\\{}q(0)=(k_{0},0,0)\land\\{}\operatorname{kappa}\left(q(\operatorname{Duration}\left(A\right))\right)=k_{0}\land \operatorname{chi}\left(q(\operatorname{Duration}\left(A\right))\right)=0\land\\{}(\forall t\in [0,\operatorname{Duration}\left(A\right)], \exists p:\operatorname{InteriorProbability}\left(4\right), \operatorname{weight}\left(p\right)=\operatorname{probability}\left(b, \operatorname{kappa}\left(q(t)\right)\right))\land\\{}(\forall t\in [0,\operatorname{Duration}\left(A\right)], \operatorname{Compatible}\left(q(t)\right))\land\\{}\operatorname{phase}\left(q(\operatorname{Duration}\left(A\right))\right)=\operatorname{residual}\left(\operatorname{phaseWeight}\left(b\right), k_{0}, A\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiniteRectangleTransport.finite_rectangles_realize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base b is the triple (X,Y,Z), with 0 < Z < 1 and 0 < X,Y < 1-Z. Its open fiber J(b) has endpoints max(0,X+Y-(1-Z)) and min(X,Y). The five probabilities, in the mode order (0,1,2,3,13), are (1-Z-X-Y+k,X-k,Z,Y-k,k). Their strict positivity and total one use the existing InteriorProbability carrier.

The direction is (1,-1,0,-1,1). The information coefficient is the sum of the four reciprocal bottom probabilities. The phase weight w is the direction divided coordinatewise by probability times information. Compatible(q(t)) asserts that the middle phase is zero and that the direction paired with the lifted phases equals the real relation phase. The state of a history q consists of the probability coordinate k, the real lifted relation phase c, and five real lifted phases v. Duration(A) is four times the length of the finite menu A; its phase target is the sum of a times (w(k)-w(k0)) over the entries (k,a).

Admissible(b,N,q) requires continuity of the actual real-time function q, probability coordinates in J(b) on the closed interval from zero to N, finite variation of c, and an affine chart on each unit-time leg. On every open leg and for every mode, the probability derivative equals the direction times the derivative of k, and the derivative of v equals w(k) times the derivative of c. It also requires integrability of every actual transport component and equality of its integral with the corresponding terminal minus initial lifted phase. Thus the supplied object is a piecewise linear control with its transported state lift and exact integral residual.

For each menu entry, the four successive vertices change k from k0 to k, change c from zero to a at k, return k to k0, and return c to zero at k0. The phase changes on the two phase legs are a times w(k) and minus a times w(k0). Concatenating these vertices gives the real-time interpolation; matching endpoints prove continuity, and affine charts give finite variation and the differential law.

All real coefficients, including negative and zero coefficients, repeated heights, either symmetry wall, and the empty menu are included. There is no uniform speed, energy or amplitude bound. This realizes every supplied finite representation; it does not establish the existence of a representation for every vector in the full holonomy space, nor the three-height basis or the compact holonomy group.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiniteRectangleTransport.finite_rectangles_realize`
- Dependency: [D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber](InteriorProbabilityPhaseFiber.md)
