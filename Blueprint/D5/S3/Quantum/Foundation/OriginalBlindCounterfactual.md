# Original blind directions and actual counterfactual states

## Abstract

Every nonzero original normalized blind direction has two actual interior states and a distinguishing full proper effect.

Let C be a closed generating cone in a finite dimensional real normed space V, with a real-linear unit u strictly positive on every nonzero cone vector. The base K is the entire set C intersect {u=1}; proper(C,u,f) means 0<=f(v)<=u(v) for every original cone vector v. The norm only presents the finite dimensional topology. The conclusion specifies original vectors and original effects, without introducing an inner product or replacing either full domain.

**Theorem 1.1 (Two interior states share the blind readout and remain distinguishable).**

$$\forall V \in Type,\; \forall O \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{AddCommGroup}\left(O\right)] [\operatorname{Module}\left(\mathbb{R}, O\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\forall T \in \operatorname{LinearMap}\left(\mathbb{R}, V, O\right),\; \forall z \in V,\; z\neq 0 \Rightarrow \left(\operatorname{apply}\left(u, z\right) = 0 \Rightarrow \left(\operatorname{apply}\left(T, z\right) = 0 \Rightarrow \left(\exists w \in V,\; \exists e \in \mathbb{R},\; \exists f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; w\in \operatorname{base}\left(C, u\right) \land \left(w\in \operatorname{interior}\left(C\right) \land \left(0< e \land \left(\operatorname{proper}\left(C, u, f\right) \land \left(w+e\cdot z\in \operatorname{base}\left(C, u\right) \land \left(w-e\cdot z\in \operatorname{base}\left(C, u\right) \land \left(w+e\cdot z\in \operatorname{interior}\left(C\right) \land \left(w-e\cdot z\in \operatorname{interior}\left(C\right) \land \left(w+e\cdot z\neq w-e\cdot z \land \left(\operatorname{apply}\left(T, w+e\cdot z\right) = \operatorname{apply}\left(T, w-e\cdot z\right) \land 0< \operatorname{apply}\left(f, w+e\cdot z\right)-\operatorname{apply}\left(f, w-e\cdot z\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalBlindCounterfactual.original_blind_direction_counterfactual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real-linear readout T into any real module O and every nonzero z with u(z)=0 and T(z)=0, there are an original normalized interior center w, a strictly positive real scale e, and an original full proper effect f. Both w+e*z and w-e*z belong to K and to the cone interior, are distinct, and have equal T-readouts. Their f-readout difference is strictly positive. No finite-output, injectivity, positivity or operational realizability assumption is made about T.

Generatingness gives nonempty cone interior. A nonzero interior vector normalizes to an interior member of K. Continuity of both signed lines through this center supplies one strictly positive common scale for the two perturbations. The same unit vanishes on z, so normalization is preserved on both sides.

Compactness bounds the norm of every point of the entire K by one positive R. A norm-one dual functional l with l(z)=norm(z) gives f=u/2+l/(2R). Its values on every pure point lie in [0,1], so the original cone bound extends these inequalities to the whole C. Since u(z)=0, f(z)>0. The signed perturbations therefore have strictly positive readout difference 2*e*f(z). This constructs a globally proper separator rather than treating the nonpositive signed vector as a state.

For a triple of original face readouts, a nonzero signed vector in their common kernel and in ker(u) satisfies these hypotheses. The result supplies actual normalized states witnessing failure of separation. The existence and algebra of those original readouts, the assertion that their blind kernel lies in ker(u), six-block norm bounds, and a common pairing require their own hypotheses and proofs. The result asserts no Jordan classification, reciprocal confirmation, or physical implementation.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalBlindCounterfactual.original_blind_direction_counterfactual`
- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](CircuitBalancedConfirmation.md)
