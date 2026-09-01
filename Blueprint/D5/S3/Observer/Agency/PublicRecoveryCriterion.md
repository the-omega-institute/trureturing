# Public Recovery Criterion

## Abstract

Public recovery through an additive observation is equivalent to kernel containment and to vanishing covert transport; adding a ledger can only shrink the covert image.

**Theorem 1.1 (Public recovery, kernel containment, and ledger refinement).**

$$\begin{gathered}\forall U, P, \mathcal{K}, \Lambda: Type,\\{}\operatorname{AddGroup}\left(U\right) \land \operatorname{AddGroup}\left(P\right) \land \operatorname{AddGroup}\left(\mathcal{K}\right) \land \operatorname{AddGroup}\left(\Lambda\right) \land\\{}H: \operatorname{AddMonoidHom}\left(U, P\right) \land K: \operatorname{AddMonoidHom}\left(U, \mathcal{K}\right) \land L: \operatorname{AddMonoidHom}\left(U, \Lambda\right) \Rightarrow\\{}\left(\left(\exists \overline{K}: \operatorname{AddMonoidHom}\left(\operatorname{im}\left(H\right), \mathcal{K}\right), K = \overline{K} \circ H \Leftrightarrow \operatorname{ker}\left(H\right) \subseteq \operatorname{ker}\left(K\right)\right) \land \left(\left(\operatorname{ker}\left(H\right) \subseteq \operatorname{ker}\left(K\right) \Leftrightarrow \operatorname{image}\left(K, \operatorname{ker}\left(H\right)\right) = 0\right) \land \left(\operatorname{image}\left(K, \operatorname{ker}\left(H\right)\right) = 0 \Leftrightarrow \exists \overline{K}: \operatorname{AddMonoidHom}\left(\operatorname{im}\left(H\right), \mathcal{K}\right), K = \overline{K} \circ H\right)\right)\right) \land \operatorname{image}\left(K, \operatorname{intersection}\left(\operatorname{ker}\left(H\right), \operatorname{ker}\left(L\right)\right)\right) \subseteq \operatorname{image}\left(K, \operatorname{ker}\left(H\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Agency/PublicRecoveryCriterion.public_recovery_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The control, public, hidden, and ledger carriers are additive groups. The public observation H, hidden transport K, and ledger L are additive homomorphisms, matching the source's uses of kernels, zero, intersection, and kernel image.

A recovery homomorphism on the realized public image exists exactly when every publicly silent control is also hidden-silent. The covert throat is represented by the additive image K(ker H), so its vanishing is the same kernel condition.

Adding the ledger replaces ker H by ker H intersect ker L. This is a subgroup of ker H, and monotonicity of additive image proves that the remaining covert transport can only shrink.

## References

- Truth anchor: `D5/S3/Observer/Agency/PublicRecoveryCriterion.public_recovery_criterion`
