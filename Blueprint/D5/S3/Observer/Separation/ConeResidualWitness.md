# Cone Residual Dual Witness

## Abstract

A closed convex cone residual gives its canonical separating dual witness.

**Theorem 1.1 (The cone residual is a dual witness).**

$$\forall E: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}(\mathbb{R}, E)],\ [\operatorname{CompleteSpace}(E)],\ C: \operatorname{ProperCone}(\mathbb{R}, E),\ x: E,\quad \operatorname{let}(p = P_{C}(x), r = x - p, w = -r);\quad w \in \operatorname{InnerDual}(C) \land (\neg (x \in C) \Rightarrow ((\forall c: E,\ c \in C \Rightarrow 0 \leq \langle w, c \rangle) \land \langle w, x \rangle = -\left\lVert r \right\rVert^{2} \land \langle w, x \rangle < 0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/ConeResidualWitness.cone_residual_observer_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a closed convex cone in an arbitrary real Hilbert space, let p be a nearest point of x in C, set r = x - p, and set w = -r. Then w belongs to the inner dual cone. If x is outside C, w is nonnegative on every point of C while its value on x is exactly minus the squared norm of r and is strictly negative.

The metric-projection variational inequality is applied at zero, twice p, and c + p. These three tests respectively give the two inequalities forcing orthogonality and the polar inequality for every c in C. The strict sign follows because a zero residual would put x in C.

Repository searches found no existing residual-duality declaration. Pinned Mathlib supplies the inner-dual definition, the Hilbert projection theorem, and the variational characterization used directly in the proof. Loogle confirmed those declarations and found no exact wrapper; LeanSearch returned only general cone infrastructure.

## References

- Truth anchor: `D5/S3/Observer/Separation/ConeResidualWitness.cone_residual_observer_duality`
