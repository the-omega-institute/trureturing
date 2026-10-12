# PsiMeanTraceConcavity

## Abstract

Hiai mean-trace concavity

**Theorem 1.1 (Joint concavity in three matrix inputs).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p, theta, t: \mathbb{R},\ \forall Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ \forall Az, Ao, Bz, Bo, Wz, Wo: \operatorname{Matrix}(d, d, \mathbb{C}),\ 0\le p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{PosDef}(Az)\land \operatorname{PosDef}(Ao)\land \operatorname{PosDef}(Bz)\land \operatorname{PosDef}(Bo)\land \operatorname{PosDef}(Wz)\land \operatorname{PosDef}(Wo)\land 0\le t\land t\le 1\implies\ (1-t)\operatorname{gamma}(p, theta, Z, Az, Bz, Wz)+t\operatorname{gamma}(p, theta, Z, Ao, Bo, Wo)\le \operatorname{gamma}(p, theta, Z, \operatorname{smul}((1-t), Az)+\operatorname{smul}(t, Ao), \operatorname{smul}((1-t), Bz)+\operatorname{smul}(t, Bo), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.gamma_triple_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every finite complex matrix dimension, arbitrary fixed Z, p and theta in [0,1], the real trace pairing Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in the three positive definite inputs. All mixtures use one common coefficient. The spectral matrix mean is transported to the genuine Hilbert-Schmidt mean through the public matrix/operator star-algebra equivalence. Generic continuous functional calculus preserves spectral powers, and the public trace-to-matrix identity preserves the real trace. Empty dimension is split explicitly.

**Theorem 1.2 (Exact mean-trace concavity).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p, theta: \mathbb{R},\ \forall Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ 0<p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{IsUnit}(Z)\implies\ \operatorname{JointlyConcaveOn}(\operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \lambda A, B\mapsto \operatorname{psi}(p, theta, Z, A, B))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.psi_jointly_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every finite complex matrix dimension, 0<p<=1, theta in [0,1] and fixed invertible complex Z, Psi(A,B)=Re Tr((Z adjoint (B^p #theta A^p) Z)^(1/p)) is jointly concave on all positive definite A,B. They may be noncommuting, and Z need not be selfadjoint. The genuine mean convention is X #theta Y=X^(1/2)(X^(-1/2) Y X^(-1/2))^theta X^(1/2). Thus B^p is the base. All powers are the actual spectral CFC powers; the outer reciprocal power is inside the trace.

Invertibility of Z makes each mean congruence positive definite. The forward trace-Young maximum is attained at W=M^(1/p). Choose these two endpoint optimizers, mix them within the positive definite cone, and apply triple joint concavity to Gamma minus its affine trace penalty. The universal Young bound at the mixture then gives p times Psi(mixture) >= p times the mixture of the two endpoint values. Division by p>0 concludes the proof. An arbitrary supremum of separately concave functions is not used. The p=1 and theta=0,1 endpoints are retained by the suppliers, and the matrix triple theorem treats empty dimension separately.

This is the classical Hiai Lemma 3.3 target, obtained by a connected Hilbert-Schmidt and tracial variational derivation. It does not settle the full open Problem 5.18 of arXiv:2510.04691v3. That problem still requires inverse-geometric identification, its original variational parameter assembly, and a source-faithful common-epsilon-I limit preserving s(A)>=s(B). No positive definite optimizer is claimed for singular M or noninvertible Z. The native four-slot escape audit remains unfinished under issue #5214; compilation is not declared_validated registration or official acceptance.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.gamma_triple_concave`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.psi_jointly_concave`
- Dependency: [D5/S3/Quantum/Hiai/ForwardTraceYoung](ForwardTraceYoung.md)
- Dependency: [D5/S3/Quantum/Hiai/HSMeanTraceConcavity](HSMeanTraceConcavity.md)
