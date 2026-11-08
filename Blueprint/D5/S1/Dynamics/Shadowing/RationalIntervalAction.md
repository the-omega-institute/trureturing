# Rational Closed Interval Action

## Abstract

Positive rational interval homeomorphisms give the exact north-south map and all its integer iterates.

Let I=[0,1]. For a positive real parameter c define action(c,u)=cu/(1-u+cu), and let H(c) denote this map as a homeomorphism of I. The denominator is positive even at both endpoints; the inverse is action(1/c,u). The map f is H(2), exactly the rationalIntervalMap used in the marker classification. The parameter is multiplicative; no real exponential or logarithmic parametrization is required.

**Theorem 1.1 (Positive denominator on the closed interval).**

$$\begin{aligned}\forall c\in \mathbb{R}, \forall u\in I, 0<c\Rightarrow 0<1-u+cu\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.denominator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For u<1 the term 1-u is positive and cu is nonnegative. At u=1 the denominator is c>0.

**Theorem 1.2 (Joint continuity on positive parameters and the closed interval).**

$$\begin{aligned}\operatorname{Continuous}((c,u)\in (0,\infty)\times I\mapsto action(c,u))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.continuous_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive denominator permits division of continuous coordinate functions on the full parameter product.

**Theorem 1.3 (Multiplicative action law).**

$$\begin{aligned}\forall c\in \mathbb{R}, \forall d\in \mathbb{R}, \forall u\in I, 0<c\land 0<d\Rightarrow action(c,action(d,u))=action(cd,u)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.action_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Clearing the positive denominators gives the action law. The unit parameter acts identically and the reciprocal parameter gives both inverse identities.

**Theorem 1.4 (All integer powers are rational actions).**

$$\begin{aligned}\forall c\in \mathbb{R}, \forall k\in \mathbb{Z}, 0<c\Rightarrow H(c)^{k}=H(c^{k})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.homeomorph_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive and negative integer induction uses the multiplication law in the homeomorphism group. In particular f to the integer power k is H(2 to the power k).

**Theorem 1.5 (The literal closed pseudo-orbit domain).**

$$\begin{aligned}\forall delta\in \mathbb{R}, \forall x:\mathbb{Z}\to I, ClosedPseudoOrbit(f,delta,x)\Leftrightarrow ClosedRationalPseudoOrbit(delta,x)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.closedPseudoOrbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left side is the existing compact-selector predicate dist(x(k+1),f(x(k)))<=delta at every integer k. The right side is the absolute-error predicate for 2u/(1+u). Symmetry of real distance identifies them, including equality in the error bound and both interval endpoints.

**Theorem 1.6 (Negative orbit limit).**

$$\begin{aligned}\forall u\in I, u<1\Rightarrow \lim_{n\to \infty}f^{-n}(u)=0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.orbit_neg_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index n ranges over natural numbers. Substituting c=(1/2)^n into the rational formula gives a numerator tending to zero and a denominator tending to 1-u>0.

**Theorem 1.7 (Positive orbit limit).**

$$\begin{aligned}\forall u\in I, 0<u\Rightarrow \lim_{n\to \infty}f^{n}(u)=1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/RationalIntervalAction.orbit_pos_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index n ranges over natural numbers. Dividing numerator and denominator by 2^n gives u/((1-u)(1/2)^n+u), whose limit is one. The two endpoints are fixed by every action parameter.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.action_mul`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.closedPseudoOrbit_iff`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.continuous_action`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.denominator_pos`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.homeomorph_zpow`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.orbit_neg_tendsto`
- Truth anchor: `D5/S1/Dynamics/Shadowing/RationalIntervalAction.orbit_pos_tendsto`
- Dependency: [D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector](CompactPseudoOrbitSelector.md)
- Dependency: [D5/S1/Dynamics/Shadowing/RationalIntervalMarkers](RationalIntervalMarkers.md)
