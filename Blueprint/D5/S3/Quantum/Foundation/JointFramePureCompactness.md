# Pure compactness from joint frames

## Abstract

Joint original three-outcome frames and point-exclusion incidence force closed and compact original pure points.

Let V be a finite dimensional real normed space, C the entire original cone, and u its original real-linear unit. The sets K=base(C,u), P=pure(C,u), the globally proper effects and the mixed-state exclusion sets are the existing CircuitBalancedConfirmation and FacetZeroGluing objects. The closed generating cone and strict positivity of u imply compactness of K. Strict positivity also excludes nonzero lines. No finiteness or closedness of P is assumed.

**Definition 1.1 (One joint three-outcome frame).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall s \in \operatorname{Fin}\left(3\right)\to V,\; \forall e \in \operatorname{Fin}\left(3\right)\to \operatorname{ContinuousLinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{jointFrame}\left(C, u, s, e\right) \Leftrightarrow \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{apply}\left(s, i\right)\in \operatorname{base}\left(C, u\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{proper}\left(C, u, \operatorname{toLinearMap}\left(\operatorname{apply}\left(e, i\right)\right)\right)\right) \land \left(\operatorname{sum}\left(e\right) = \operatorname{toContinuousLinearMap}\left(u\right) \land \left(\forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{apply}\left(\operatorname{apply}\left(e, i\right), \operatorname{apply}\left(s, j\right)\right) = \operatorname{Kronecker}\left(i, j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/JointFramePureCompactness.jointFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three states belong to the entire original base. Each effect is nonnegative and bounded above by u on the entire original cone; their sum equals u as a functional on V. All nine state-effect readings are Kronecker readings, with Kronecker(i,j)=1 for i=j and 0 otherwise. The notation sum(e) sums over Fin 3. Continuous linear effects exhaust real-linear effects because V is finite dimensional; no restricted menu is introduced.

**Definition 1.2 (Complete every original pure point).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{pureJointCompletion}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \exists s \in \operatorname{Fin}\left(3\right)\to V,\; \exists e \in \operatorname{Fin}\left(3\right)\to \operatorname{ContinuousLinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{apply}\left(s, i\right)\in \operatorname{pure}\left(C, u\right)\right) \land \left(\operatorname{apply}\left(s, 0\right) = p \land \operatorname{jointFrame}\left(C, u, s, e\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/JointFramePureCompactness.pureJointCompletion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each p in the entire original pure set, there exist three original pure states and three original globally proper effects forming a jointFrame, with the first state equal to p. Each p may have many completions. The theorem requires neither continuity nor uniqueness of a selected completion.

**Definition 1.3 (Incidence of entire original exclusions).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{pointBallIncidence}\left(C, u\right) \Leftrightarrow \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; \operatorname{exclusion}\left(C, u, p\right)\neq \operatorname{exclusion}\left(C, u, q\right) \Rightarrow \operatorname{Subsingleton}\left(\operatorname{inter}\left(\operatorname{exclusion}\left(C, u, p\right), \operatorname{exclusion}\left(C, u, q\right)\right)\right)\right) \land \operatorname{Injective}\left(\operatorname{exclusionOnPure}\left(C, u\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/JointFramePureCompactness.pointBallIncidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For pure p and q with different entire exclusion sets, their intersection is a subsingleton. In addition, the map p to exclusion(C,u,p) on the subtype of all original pure points is injective. exclusionOnPure denotes exactly this map. No selected faces, selected pure subset or new orthogonality relation replaces the original exclusions.

**Theorem 1.4 (The entire pure set is closed).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{pureJointCompletion}\left(C, u\right) \Rightarrow \left(\operatorname{pointBallIncidence}\left(C, u\right) \Rightarrow \operatorname{IsClosed}\left(\operatorname{pure}\left(C, u\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/JointFramePureCompactness.pure_closed_of_joint_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume closedness and generation of the original cone, strict positivity of its original unit, pureJointCompletion and pointBallIncidence. Then all extreme points of the entire original base form a closed subset of V, hence also a relatively closed subset of K.

First consider one globally proper effect a confirming x and vanishing at two distinct original states y,z. Its one-face F is nonempty, compact, convex and exposed. Every extreme point of F is an original pure point. For two such points p,q, the same effect a puts both y and z in both original exclusions. The intersection condition forces those exclusions equal; injectivity gives p=q. Krein-Milman identifies F with the closed convex hull of its extreme points, so F is a singleton and x is pure. The two excluded states need not themselves be pure.

The full proper-effect interval is compact: a finite basis chosen from the generating cone bounds every effect reading between zero and the original unit reading. The basis operator-norm estimate gives boundedness, while all cone inequalities are closed. Take the compact product of three original states and three such effects. The joint unit and all nine Kronecker equations define a closed subset T of this same product. Evaluation is continuous jointly in state and effect. Any frame in T has distinct second and third states, distinguished by its second effect, so the preceding one-face argument proves its first state pure. Conversely pureJointCompletion puts every original pure point in the first-coordinate image of T. This image is compact and hence closed; all joint relations are retained together.

**Theorem 1.5 (The entire pure set is compact).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{pureJointCompletion}\left(C, u\right) \Rightarrow \left(\operatorname{pointBallIncidence}\left(C, u\right) \Rightarrow \operatorname{IsCompact}\left(\operatorname{pure}\left(C, u\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/JointFramePureCompactness.pure_compact_of_joint_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same hypotheses, P is compact. Apply the closedness conclusion inside the compact original base K using the existing inclusion of extreme points in their ambient set. Empty bases and empty pure sets are included. The one-face argument chooses an extreme point only after establishing a nonempty compact face.

These are conditional consequences of joint completion and point-exclusion incidence on the original full domain. They express the compactness inference used in Quantum Origin VII, Theorem 104.6. Deriving both predicates from the original exclusion-ball condition EB of dimension at least one and the original orthogonal-pair proper-face condition remains a further mathematical obligation; these theorems do not assert that derivation or the full EB-plus-Pair theorem. They assume no spectrality, self-duality, projectivity, unique effect selection, global least confirmation or physical implementation. No literature priority is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/JointFramePureCompactness.jointFrame`
- Truth anchor: `D5/S3/Quantum/Foundation/JointFramePureCompactness.pointBallIncidence`
- Truth anchor: `D5/S3/Quantum/Foundation/JointFramePureCompactness.pureJointCompletion`
- Truth anchor: `D5/S3/Quantum/Foundation/JointFramePureCompactness.pure_closed_of_joint_completion`
- Truth anchor: `D5/S3/Quantum/Foundation/JointFramePureCompactness.pure_compact_of_joint_completion`
- Dependency: [D5/S3/Quantum/Foundation/FacetZeroGluing](FacetZeroGluing.md)
