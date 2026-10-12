# HSCommonRightMean

## Abstract

HSCommonRightMean

**Theorem 1.1 (Strict positivity of the action product).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall X, D: \operatorname{L}(H),\ \operatorname{pdSet}(X)\land \operatorname{pdSet}(D)\implies\ \operatorname{pdSet}(\operatorname{lr}(X, D))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/HSCommonRightMean.lr_pd` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

The product of left multiplication by strictly positive X and right multiplication by strictly positive D is strictly positive on the true HS space. Left and right actions commute, even when the original operators do not.

**Theorem 1.2 (All real powers of the HS product).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall s: \mathbb{R},\ \forall X, D: \operatorname{L}(H),\ \operatorname{pdSet}(X)\land \operatorname{pdSet}(D)\implies\ \operatorname{rpow}(\operatorname{lr}(X, D), s)=\operatorname{lr}(\operatorname{rpow}(X, s), \operatorname{rpow}(D, s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/HSCommonRightMean.lr_power` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every real s, (L_X R_D)^s = L_(X^s) R_(D^s) on finite nontrivial complex Hilbert space. The full public perspective identity gives the normalized power after cancellation of the invertible right square-root sandwich. Substituting the inverse of D recovers arbitrary powers. Right multiplication reverses products, and every combined right factor here is a power of this same D.

**Theorem 1.3 (Common right factor in the genuine mean).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall theta: \mathbb{R},\ \forall X, Y, D: \operatorname{L}(H),\ \operatorname{pdSet}(X)\land \operatorname{pdSet}(Y)\land \operatorname{pdSet}(D)\implies\ \operatorname{mean}(theta, \operatorname{lr}(X, D), \operatorname{lr}(Y, D))=\operatorname{lr}(\operatorname{mean}(theta, X, Y), D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/HSCommonRightMean.mean_lr_common` (`✓ std3`). ∎

*Citation.* Fumio Hiai (2015). *Concavity of certain matrix trace and norm functions. II*. URL: <https://arxiv.org/abs/1507.00853v3>.

*Commentary.*

For every real theta, the genuine mean of L_X R_D and L_Y R_D is L_(X #theta Y) R_D. In the normalized middle the right factors D^(-1/2), D, D^(-1/2) cancel; the outer two D^(1/2) factors multiply to D. X and Y may be noncommuting. The triple-variable concavity theorem uses this exact identity.

These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/HSCommonRightMean.lr_pd`
- Truth anchor: `D5/S3/Quantum/Hiai/HSCommonRightMean.lr_power`
- Truth anchor: `D5/S3/Quantum/Hiai/HSCommonRightMean.mean_lr_common`
- Dependency: [D5/S3/Quantum/Hiai/HSPowerProduct](HSPowerProduct.md)
