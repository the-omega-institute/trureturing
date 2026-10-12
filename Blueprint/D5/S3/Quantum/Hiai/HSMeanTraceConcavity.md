# HSMeanTraceConcavity

## Abstract

HSMeanTraceConcavity

**Theorem 1.1 (Triple operator concavity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall p, theta, t: \mathbb{R},\ \forall Az, Ao, Bz, Bo, Wz, Wo: \operatorname{L}(H),\ 0\le p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{pdSet}(Az)\land \operatorname{pdSet}(Ao)\land \operatorname{pdSet}(Bz)\land \operatorname{pdSet}(Bo)\land \operatorname{pdSet}(Wz)\land \operatorname{pdSet}(Wo)\land 0\le t\land t\le 1\implies\ \operatorname{smul}((1-t), \operatorname{mean}(theta, \operatorname{powerProduct}(p, Bz, Wz), \operatorname{powerProduct}(p, Az, Wz)))+\operatorname{smul}(t, \operatorname{mean}(theta, \operatorname{powerProduct}(p, Bo, Wo), \operatorname{powerProduct}(p, Ao, Wo)))\le \operatorname{mean}(theta, \operatorname{powerProduct}(p, \operatorname{smul}((1-t), Bz)+\operatorname{smul}(t, Bo), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo)), \operatorname{powerProduct}(p, \operatorname{smul}((1-t), Az)+\operatorname{smul}(t, Ao), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/HSMeanTraceConcavity.meanProduct_triple_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For p and theta in [0,1], form P_p(X,W)=L_(X^p) R_(W^(1-p)). Its joint operator concavity follows from the public full HS perspective identity and all-Hilbert power-perspective concavity. Mix A, B and W with one common coefficient. Both-input mean monotonicity compares the endpoint mixtures with the two Lieb lifts at the mixture; joint mean concavity then yields the triple operator inequality.

**Theorem 1.2 (Triple trace concavity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall p, theta, t: \mathbb{R},\ \forall Z: \operatorname{L}(H),\ \forall Az, Ao, Bz, Bo, Wz, Wo: \operatorname{L}(H),\ 0\le p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{pdSet}(Az)\land \operatorname{pdSet}(Ao)\land \operatorname{pdSet}(Bz)\land \operatorname{pdSet}(Bo)\land \operatorname{pdSet}(Wz)\land \operatorname{pdSet}(Wo)\land 0\le t\land t\le 1\implies\ (1-t)\operatorname{gamma}(p, theta, Z, Az, Bz, Wz)+t\operatorname{gamma}(p, theta, Z, Ao, Bo, Wo)\le \operatorname{gamma}(p, theta, Z, \operatorname{smul}((1-t), Az)+\operatorname{smul}(t, Ao), \operatorname{smul}((1-t), Bz)+\operatorname{smul}(t, Bo), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/HSMeanTraceConcavity.gamma_triple_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For arbitrary fixed Z, Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in all three strictly positive inputs, for p and theta in [0,1]. The common-right-factor identity identifies the HS geometric mean. Evaluation at the fixed HS vector Z preserves the operator inequality. No positivity is asserted for the nonsymmetric product inside the trace, and Z may be singular or zero. This is the joint auxiliary-variable inequality required for endpoint-optimizer interpolation.

These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/HSMeanTraceConcavity.gamma_triple_concave`
- Truth anchor: `D5/S3/Quantum/Hiai/HSMeanTraceConcavity.meanProduct_triple_concave`
- Dependency: [D5/S3/Quantum/Hiai/HSCommonRightMean](HSCommonRightMean.md)
