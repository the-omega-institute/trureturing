# Horizontal Joint Kernel

## Abstract

A finite family of positive prime-power residue channels has product-modulus kernel.

**Theorem 1.1 (The joint residue kernel is divisibility by the product modulus).**

$$\begin{gathered}S: \operatorname{Finset}\left(\mathbb{N}\right),\quad \forall p \in S, \operatorname{Prime}\left(p\right),\\{}\kappa: S \to \operatorname{PNat}\left(\right),\quad x, y \in \mathbb{Z},\\{}\operatorname{jointReadout}\left((z \mapsto z \bmod p^{\kappa(p)})_{p \in S}, x\right) = \operatorname{jointReadout}\left((z \mapsto z \bmod p^{\kappa(p)})_{p \in S}, y\right)\\{}\iff \prod_{p \in S} p^{\kappa(p)} \mid (x - y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/HorizontalJointKernel.horizontal_joint_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a finite set of natural numbers, require every member of S to be prime, and assign each selected prime a positive natural precision. The readout is constructed from the integer reduction channel modulo p raised to that precision at every p in S.

Two integers have equal joint readouts exactly when their difference is divisible by the product of the selected prime powers. Pairwise coprimality of distinct selected primes combines the component divisibilities, while every component modulus divides the product for the reverse implication.

The declaration uses the existing jointReadout family primitive and the library equivalence between equality in ZMod and divisibility of an integer difference. It introduces no parallel readout or product-modulus definition.

## References

- Truth anchor: `D5/S3/Arith/Congruence/HorizontalJointKernel.horizontal_joint_kernel`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
