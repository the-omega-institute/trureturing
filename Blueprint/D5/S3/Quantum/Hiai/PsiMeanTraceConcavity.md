# PsiMeanTraceConcavity

## Abstract

Exact Hiai mean-trace concavity through the Hilbert-Schmidt lift and forward trace Young.

**Theorem 1.1 (Full HS perspective identity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall s: \mathbb{R},\ \forall A, B: \operatorname{L}(H),\ \operatorname{pdSet}(A)\land \operatorname{pdSet}(B)\implies\ \operatorname{operatorPowerMean}(s, 1, \operatorname{leftMulHS}(A), \operatorname{rightMulHS}(B))=\operatorname{leftMulHS}(\operatorname{rpow}(A, s))\operatorname{rightMulHS}(\operatorname{rpow}(B, (1-s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.perspective_lr_eq` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

On a finite nontrivial complex Hilbert space and for every real s, the perspective of leftMulHS A and rightMulHS B equals leftMulHS(A^s) rightMulHS(B^(1-s)). The public arbitrary-K scalar bridge is applied with K=V adjoint for every HS vector V. Selfadjointness and complex polarization convert equality of real quadratic forms to operator equality. This supplies the product powers used by the common-right-factor mean.

**Theorem 1.2 (Strict positivity of the action product).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall X, D: \operatorname{L}(H),\ \operatorname{pdSet}(X)\land \operatorname{pdSet}(D)\implies\ \operatorname{pdSet}(\operatorname{lr}(X, D))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.lr_pd` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

The product of left multiplication by strictly positive X and right multiplication by strictly positive D is strictly positive on the true HS space. Left and right actions commute, even when the original operators do not.

**Theorem 1.3 (All real powers of the HS product).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall s: \mathbb{R},\ \forall X, D: \operatorname{L}(H),\ \operatorname{pdSet}(X)\land \operatorname{pdSet}(D)\implies\ \operatorname{rpow}(\operatorname{lr}(X, D), s)=\operatorname{lr}(\operatorname{rpow}(X, s), \operatorname{rpow}(D, s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.lr_power` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every real s, (L_X R_D)^s = L_(X^s) R_(D^s) on finite nontrivial complex Hilbert space. The full public perspective identity gives the normalized power after cancellation of the invertible right square-root sandwich. Substituting the inverse of D recovers arbitrary powers. Right multiplication reverses products, and every combined right factor here is a power of this same D.

**Theorem 1.4 (Common right factor in the genuine mean).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall theta: \mathbb{R},\ \forall X, Y, D: \operatorname{L}(H),\ \operatorname{pdSet}(X)\land \operatorname{pdSet}(Y)\land \operatorname{pdSet}(D)\implies\ \operatorname{mean}(theta, \operatorname{lr}(X, D), \operatorname{lr}(Y, D))=\operatorname{lr}(\operatorname{mean}(theta, X, Y), D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.mean_lr_common` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every real theta, the genuine mean of L_X R_D and L_Y R_D is L_(X #theta Y) R_D. In the normalized middle the right factors D^(-1/2), D, D^(-1/2) cancel; the outer two D^(1/2) factors multiply to D. X and Y may be noncommuting. The triple-variable concavity theorem uses this exact identity.

**Theorem 1.5 (Triple operator concavity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall p, theta, t: \mathbb{R},\ \forall Az, Ao, Bz, Bo, Wz, Wo: \operatorname{L}(H),\ 0\le p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{pdSet}(Az)\land \operatorname{pdSet}(Ao)\land \operatorname{pdSet}(Bz)\land \operatorname{pdSet}(Bo)\land \operatorname{pdSet}(Wz)\land \operatorname{pdSet}(Wo)\land 0\le t\land t\le 1\implies\ \operatorname{smul}((1-t), \operatorname{mean}(theta, \operatorname{powerProduct}(p, Bz, Wz), \operatorname{powerProduct}(p, Az, Wz)))+\operatorname{smul}(t, \operatorname{mean}(theta, \operatorname{powerProduct}(p, Bo, Wo), \operatorname{powerProduct}(p, Ao, Wo)))\le \operatorname{mean}(theta, \operatorname{powerProduct}(p, \operatorname{smul}((1-t), Bz)+\operatorname{smul}(t, Bo), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo)), \operatorname{powerProduct}(p, \operatorname{smul}((1-t), Az)+\operatorname{smul}(t, Ao), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.meanProduct_triple_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For p and theta in [0,1], form P_p(X,W)=L_(X^p) R_(W^(1-p)). Its joint operator concavity follows from the public full HS perspective identity and all-Hilbert power-perspective concavity. Mix A, B and W with one common coefficient. Both-input mean monotonicity compares the endpoint mixtures with the two Lieb lifts at the mixture; joint mean concavity then yields the triple operator inequality.

**Theorem 1.6 (Triple trace concavity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall p, theta, t: \mathbb{R},\ \forall Z: \operatorname{L}(H),\ \forall Az, Ao, Bz, Bo, Wz, Wo: \operatorname{L}(H),\ 0\le p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{pdSet}(Az)\land \operatorname{pdSet}(Ao)\land \operatorname{pdSet}(Bz)\land \operatorname{pdSet}(Bo)\land \operatorname{pdSet}(Wz)\land \operatorname{pdSet}(Wo)\land 0\le t\land t\le 1\implies\ (1-t)\operatorname{gamma}(p, theta, Z, Az, Bz, Wz)+t\operatorname{gamma}(p, theta, Z, Ao, Bo, Wo)\le \operatorname{gamma}(p, theta, Z, \operatorname{smul}((1-t), Az)+\operatorname{smul}(t, Ao), \operatorname{smul}((1-t), Bz)+\operatorname{smul}(t, Bo), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.hs_gamma_triple_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For arbitrary fixed Z, Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in all three strictly positive inputs, for p and theta in [0,1]. The common-right-factor identity identifies the HS geometric mean. Evaluation at the fixed HS vector Z preserves the operator inequality. No positivity is asserted for the nonsymmetric product inside the trace, and Z may be singular or zero. This is the joint auxiliary-variable inequality required for endpoint-optimizer interpolation.

**Theorem 1.7 (Forward tracial Young inequality).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p: \mathbb{R},\ \forall M, W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(M)\land \operatorname{PosDef}(W)\land 0<p\land p\le 1\implies\ \operatorname{objective}(p, M, W)\le p\operatorname{tracePower}(\frac{1}{p}, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.forward_trace_young` (`✓ std3`). ∎

*Citation.* Eric A. Carlen and Elliott H. Lieb (2008). *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II*. URL: <https://arxiv.org/abs/0710.4167v3>.

*Commentary.*

For all finite complex matrix dimensions, positive definite M and W and 0<p<=1, Re Tr(M W^(1-p))-(1-p) Re Tr W <= p Re Tr(M^(1/p)). For 0<p<1, apply the existing Schatten Holder supplier to M^(1/2) W^((1-p)/2) at exponents 2, 2/p and 2/(1-p). The public column-Gram identity and trace cyclicity give the mixed trace. Raising the bound to two and applying scalar weighted Young proves the result. The endpoint p=1 is calculated separately. Empty dimension and noncommuting M,W are retained.

**Theorem 1.8 (Explicit attained maximum).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p: \mathbb{R},\ \forall M: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(M)\land 0<p\land p\le 1\implies\ \exists W: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(W)\land W=\operatorname{rpow}(M, \frac{1}{p})\land \operatorname{objective}(p, M, W)=p\operatorname{tracePower}(\frac{1}{p}, M)\land (\forall V: \operatorname{Matrix}(d, d, \mathbb{C}),\ \operatorname{PosDef}(V)\implies\ \operatorname{objective}(p, M, V)\le \operatorname{objective}(p, M, W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.maximum_and_attainment` (`✓ std3`). ∎

*Citation.* Eric A. Carlen and Elliott H. Lieb (2008). *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II*. URL: <https://arxiv.org/abs/0710.4167v3>.

*Commentary.*

An explicit positive definite maximizer is W0=M^(1/p), and the objective equals p Re Tr(M^(1/p)) there and dominates its value at every positive definite W. At p=1 the objective is independent of W, so uniqueness is not asserted. The equality uses same-matrix spectral power arithmetic. No positive definite optimizer is asserted for singular M. The mean-trace concavity proof interpolates the two actual endpoint optimizers; it needs joint concavity in the auxiliary variable, not a supremum of separately concave functions.

**Theorem 1.9 (Joint concavity in three matrix inputs).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p, theta, t: \mathbb{R},\ \forall Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ \forall Az, Ao, Bz, Bo, Wz, Wo: \operatorname{Matrix}(d, d, \mathbb{C}),\ 0\le p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{PosDef}(Az)\land \operatorname{PosDef}(Ao)\land \operatorname{PosDef}(Bz)\land \operatorname{PosDef}(Bo)\land \operatorname{PosDef}(Wz)\land \operatorname{PosDef}(Wo)\land 0\le t\land t\le 1\implies\ (1-t)\operatorname{gamma}(p, theta, Z, Az, Bz, Wz)+t\operatorname{gamma}(p, theta, Z, Ao, Bo, Wo)\le \operatorname{gamma}(p, theta, Z, \operatorname{smul}((1-t), Az)+\operatorname{smul}(t, Ao), \operatorname{smul}((1-t), Bz)+\operatorname{smul}(t, Bo), \operatorname{smul}((1-t), Wz)+\operatorname{smul}(t, Wo))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.gamma_triple_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every finite complex matrix dimension, arbitrary fixed Z, p and theta in [0,1], the real trace pairing Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in the three positive definite inputs. All mixtures use one common coefficient. The spectral matrix mean is transported to the genuine Hilbert-Schmidt mean through the public matrix/operator star-algebra equivalence. Generic continuous functional calculus preserves spectral powers, and the public trace-to-matrix identity preserves the real trace. Empty dimension is split explicitly.

**Theorem 1.10 (Exact mean-trace concavity).**

$$\forall u: \operatorname{Level}(),\ \forall d: \operatorname{Type}(u),\ [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ \forall p, theta: \mathbb{R},\ \forall Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ 0<p\land p\le 1\land 0\le theta\land theta\le 1\land \operatorname{IsUnit}(Z)\implies\ \operatorname{JointlyConcaveOn}(\operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \lambda A, B\mapsto \operatorname{psi}(p, theta, Z, A, B))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.psi_jointly_concave` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every finite complex matrix dimension, 0<p<=1, theta in [0,1] and fixed invertible complex Z, Psi(A,B)=Re Tr((Z adjoint (B^p #theta A^p) Z)^(1/p)) is jointly concave on all positive definite A,B. They may be noncommuting, and Z need not be selfadjoint. The genuine mean convention is X #theta Y=X^(1/2)(X^(-1/2) Y X^(-1/2))^theta X^(1/2). Thus B^p is the base. All powers are the actual spectral CFC powers; the outer reciprocal power is inside the trace.

Invertibility of Z makes each mean congruence positive definite. The forward trace-Young maximum is attained at W=M^(1/p). Choose these two endpoint optimizers, mix them within the positive definite cone, and apply triple joint concavity to Gamma minus its affine trace penalty. The universal Young bound at the mixture then gives p times Psi(mixture) >= p times the mixture of the two endpoint values. Division by p>0 concludes the proof. An arbitrary supremum of separately concave functions is not used. The p=1 and theta=0,1 endpoints are retained by the suppliers, and the matrix triple theorem treats empty dimension separately.

This is the classical Hiai Lemma 3.3 target, obtained by a connected Hilbert-Schmidt and tracial variational derivation. It does not settle the full open Problem 5.18 of arXiv:2510.04691v3. That problem still requires inverse-geometric identification, its original variational parameter assembly, and a source-faithful common-epsilon-I limit preserving s(A)>=s(B). No positive definite optimizer is claimed for singular M or noninvertible Z. Compilation is not an official acceptance claim.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.forward_trace_young`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.gamma_triple_concave`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.hs_gamma_triple_concave`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.lr_pd`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.lr_power`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.maximum_and_attainment`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.meanProduct_triple_concave`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.mean_lr_common`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.perspective_lr_eq`
- Truth anchor: `D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.psi_jointly_concave`
- Dependency: [D5/S3/Quantum/Hiai/GeometricMeanOrder](GeometricMeanOrder.md)
- Dependency: [D5/S3/Quantum/Hiai/InverseMeanVariational](InverseMeanVariational.md)
