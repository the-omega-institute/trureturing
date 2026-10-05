# Product Orbits of Two Perfect Matchings

## Abstract

Two fixed-point-free involutions split every matching component into two integer-power orbits of their product.

Let s and t be involutions of any type, and let r = s * t, with t applied first. Connectivity means a finite path of s-edges and t-edges. Rotation orbits use all integer powers of r and include singleton orbits. No finiteness or freeness of the rotation action is assumed. In the formulas Component(s,t,x) is the set of y connected to x; OrbitClasses(r,C) is the set of RotationOrbit(r,y) for y in C; PairSet(A,B) is {A,B}.

**Theorem 1.1 (Excluding Reflection Stabilizers).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Leftrightarrow \left(\forall k \in Int,\; \forall x \in X,\; \left(\left(s \cdot t\right)^{k} \cdot s\right)\left(x\right) \ne x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both generators have no fixed points exactly when every r^k s has no fixed points. For even k = 2j the reflection is conjugate to s by r^j; for odd k = 2j + 1 it is conjugate to t by r^(j+1). This covers negative exponents as well.

**Theorem 1.2 (The Matching Edge Separates Product Orbits).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Leftrightarrow \left(\forall x \in X,\; \neg \operatorname{SameCycle}\left(s \cdot t, x, s\left(x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_rotation_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both generators have no fixed points exactly when s(x) lies outside the r-orbit of x for every x. An intersection would give a reflection fixing x. Conversely, an s-fixed point violates separation at exponent zero, and a t-fixed point violates it at exponent one.

**Theorem 1.3 (Exact Alternating Reachability).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\forall x \in X,\; \forall y \in X,\; \operatorname{Connected}\left(s, t, x, y\right) \Leftrightarrow \left(\operatorname{SameCycle}\left(s \cdot t, x, y\right) \lor \operatorname{SameCycle}\left(s \cdot t, s\left(x\right), y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.connected_iff_rotation_orbits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary involutions, y is connected to x exactly when it lies in the r-orbit of x or in the r-orbit of s(x). Path induction gives the forward implication; positive and negative product powers give actual paths for the reverse implication. The two candidates may coincide when a generator has a fixed point.

**Theorem 1.4 (Disjoint Components and Matching Exchange).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Rightarrow \left(\forall x \in X,\; \operatorname{Disjoint}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right), \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \left(\operatorname{Component}\left(s, t, x\right) = \operatorname{Union}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right), \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \left(\operatorname{Image}\left(s, \operatorname{RotationOrbit}\left(s \cdot t, x\right)\right) = \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right) \land \operatorname{Image}\left(t, \operatorname{RotationOrbit}\left(s \cdot t, x\right)\right) = \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both involutions have no fixed points, the two product orbits are nonempty and disjoint, and their union is precisely the matching component of x. The images of the first orbit under either s or t equal the second orbit; involutivity also exchanges them in the reverse direction.

**Theorem 1.5 (Exactly Two Product Orbit Classes).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Rightarrow \left(\forall x \in X,\; \operatorname{OrbitClasses}\left(s \cdot t, \operatorname{Component}\left(s, t, x\right)\right) = \operatorname{PairSet}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right), \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \operatorname{RotationOrbit}\left(s \cdot t, x\right) \ne \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_orbit_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of all product orbits represented inside one matching component is precisely the pair of distinct orbits represented by x and s(x). If s = t, the product is the identity and each matching component still has two distinct singleton product orbits.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_orbit_classes`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_split`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.connected_iff_rotation_orbits`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_rotation_separation`
