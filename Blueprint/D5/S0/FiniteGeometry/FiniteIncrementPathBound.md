# Uniform Bounds for Finite Increment Paths

## Abstract

A fixed finite increment set bounds every finite admissible path uniformly in its length and schedule.

**Theorem 1.1 (A bound chosen before the path).**

$$\begin{aligned}\forall E: \operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)],\\\forall V: \operatorname{Finset}\left(E\right), \exists C: \mathbb{R}, 0 \leq C \land\\\forall N: \mathbb{N}, w: \mathbb{N} \to E, w\left(0\right) = 0 \Rightarrow\\(\forall k: \mathbb{N}, k < N \Rightarrow (w\left(k + 1\right) - w\left(k\right) \in V \land \langle w\left(k\right), w\left(k + 1\right) - w\left(k\right)\rangle \leq 0)) \Rightarrow\\\forall k: \mathbb{N}, k \leq N \Rightarrow \operatorname{norm}\left(w\left(k\right)\right) \leq C.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/FiniteGeometry/FiniteIncrementPathBound.exists_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any finite-dimensional real inner-product space and V a finite set of vectors. There is a nonnegative constant C, depending only on V and the fixed space, such that every path from zero whose first N increments lie in V and have nonpositive inner product with the current state has norm at most C at every index through N. The values after N are arbitrary. The increment rule allows equality, including the first step from zero. Empty sets, zero vectors and zero-dimensional spaces are included.

For each point u of the ambient unit sphere, finiteness of V gives a radius 0 < delta <= 1/2 such that a direction within delta of u can use only increments with nonpositive projection onto u. Indeed every increment with positive projection at u retains positive projection in a sufficiently small neighborhood. Compactness selects finitely many open caps of radius delta/2 covering the ambient sphere. These caps and M = 1 + sum of the increment norms are fixed before the path.

For a finite path let R be its maximum norm. If R is positive, select a cap containing the direction of a maximizing state y. For its center u and radius delta put a = 1 - delta^2/2 and b = 1 - delta^2/8. The cap gives <u,y> > bR. Any state x with <u,x> >= aR has direction within delta of u, since its norm is at most R. Its next projection cannot increase. Below aR, one increment changes the projection by at most M. Induction from zero therefore gives <u,w(k)> <= aR + M throughout the path, including after repeated exits and returns. At y this implies (3 delta^2/8) R < M. Summing the positive per-cap bounds 8M/(3 delta^2) and adding one gives a single C for every length and every schedule. If R is zero the conclusion is immediate; an empty cap cover excludes R > 0.

For a fixed finite step set in an integer lattice with a fixed positive-definite quadratic form, an isometric change of coordinates turns the nonpositive quadratic pairing rule into this inner product rule. The resulting bounded ellipsoid contains only finitely many integer states. This is an application conditional on that change of coordinates and lattice discreteness; no matrix specialization or conclusion about oscillator generation is asserted by the theorem here.

## References

- Truth anchor: `D5/S0/FiniteGeometry/FiniteIncrementPathBound.exists_uniform_bound`
