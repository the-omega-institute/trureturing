# GeometricMeanOrder

## Abstract

GeometricMeanOrder

**Theorem 1.1 (Base convention).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \forall theta: \mathbb{R},\ \forall A, B: \operatorname{L}(H),\ \operatorname{pdSet}(B)\land 0\le A\implies\ \operatorname{mean}(theta, B, A)=\operatorname{operatorPowerMean}(theta, 1, A, B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_eq_operatorPowerMean` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every complete nontrivial complex Hilbert space, nonnegative A and strictly positive B, the base-first genuine mean equals operatorPowerMean(theta,1,A,B). No order of multiplication is reversed. The inner congruence is nonnegative and all inverse powers apply to the strictly positive base.

**Theorem 1.2 (Joint mean concavity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \forall theta: \mathbb{R},\ 0\le theta\land theta\le 1\implies\ \operatorname{JointlyConcaveOn}(\operatorname{pdCone}(\operatorname{L}(H)), \operatorname{pdCone}(\operatorname{L}(H)), \lambda B, A\mapsto \operatorname{mean}(theta, B, A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_jointlyConcave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every theta in [0,1] the genuine mean is jointly operator concave on the strictly positive cone. The existing all-Hilbert perspective theorem supplies this inequality with the local base in its second argument.

**Theorem 1.3 (Monotonicity of the base).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \forall theta: \mathbb{R},\ \forall A, B, C: \operatorname{L}(H),\ 0\le theta\land theta\le 1\land \operatorname{pdSet}(B)\land \operatorname{pdSet}(C)\land 0\le A\land B\le C\implies\ \operatorname{mean}(theta, B, A)\le \operatorname{mean}(theta, C, A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_left` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

If B <= Bprime are strictly positive and A is nonnegative, increasing B increases its genuine mean with A for every theta in [0,1]. Set C=sqrt(B) sqrt(Bprime inverse); C adjoint C <= I. Contraction Jensen for the negative power function gives the required middle inequality. Congruence by sqrt(Bprime) cancels the invertible factors. No B/A commutation is used.

**Theorem 1.4 (Monotonicity of the other input).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \forall theta: \mathbb{R},\ \forall A, B, C: \operatorname{L}(H),\ 0\le theta\land theta\le 1\land A\le C\implies\ \operatorname{mean}(theta, B, A)\le \operatorname{mean}(theta, B, C)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_right` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

Increasing A increases the genuine mean with fixed B, for theta in [0,1]. Loewner-Heinz monotonicity is applied between the two square-root congruences. The both-input theorem uses this inequality after increasing the base.

**Theorem 1.5 (Both-input order).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \forall theta: \mathbb{R},\ \forall A, B, C, E: \operatorname{L}(H),\ 0\le theta\land theta\le 1\land \operatorname{pdSet}(B)\land \operatorname{pdSet}(C)\land 0\le A\land B\le C\land A\le E\implies\ \operatorname{mean}(theta, B, A)\le \operatorname{mean}(theta, C, E)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

Increasing both strictly positive bases and the nonnegative second inputs increases the mean for theta in [0,1]. The comparison composes base monotonicity and Loewner-Heinz monotonicity.

These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_eq_operatorPowerMean`
- Truth anchor: `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_jointlyConcave`
- Truth anchor: `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono`
- Truth anchor: `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_left`
- Truth anchor: `D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_right`
- Dependency: [D5/S3/Quantum/Lieb/LiebConcavity](../Lieb/LiebConcavity.md)
- Dependency: [D5/S3/Quantum/Lieb/OperatorGeometricMean](../Lieb/OperatorGeometricMean.md)
