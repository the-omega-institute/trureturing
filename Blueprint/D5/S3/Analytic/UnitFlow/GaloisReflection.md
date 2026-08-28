# Galois Reflection of the Golden Unit Flow

## Abstract

Galois conjugation reflects the Golden unit-flow principal zeta and completes its regulator periodicity to a faithful infinite-dihedral symmetry.

**Theorem 1.1 (Galois reflection and infinite-dihedral invariance).**

$$Kphi = QuadraticAlgebra(\mathbb{Q}, 1, 1),\\p = 2 \log(\varphi),\\H1 = \{s \in \mathbb{C} \mid 1 < \Re(s)\},\\\forall s \in H1,\\{}Periodic(Zs, p)\\\longrightarrow\\{}[\forall eta \in \mathbb{R}, Zs(eta) = Zs(-eta)] \land\\\operatorname{Injective}(Ap: DihedralGroup(0) \to Perm(\mathbb{R})) \land\\{}[\forall g \in DihedralGroup(0), \forall eta \in \mathbb{R}, Zs(Ap(g)(eta)) = Zs(eta)].$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/UnitFlow/GaloisReflection.galois_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lean fixes the source field itself as the Mathlib quadratic algebra K_phi = QuadraticAlgebra(Q, 1, 1), whose generator satisfies omega^2 = omega + 1. The two algebra embeddings send omega to the golden ratio phi and its real conjugate psi. The star involution is the nonidentity Galois automorphism and exchanges these distinct embeddings.

For nonzero algebraic integers alpha, the definitions set a(alpha) and b(alpha) to the squared absolute values under those fixed embeddings, Q_eta(alpha) = exp(eta)a(alpha) + exp(-eta)b(alpha), and Z_s(eta) to the complex-power sum. The source domain Re(s) > 1 is carried by the subtype H1, and regulator periodicity is the sole public premise.

Restricting the fixed star automorphism with Mathlib's RingOfIntegers.mapAlgEquiv reindexes the raw tsum after Q_eta(tau(alpha)) = Q_(-eta)(alpha). Here A_p is the displayed Lean monoid homomorphism from Mathlib's DihedralGroup 0 to permutations of the real parameter line: A_p(r_k)(eta) = eta + k p and A_p(sr_k)(eta) = -eta - k p. The theorem concludes all three conjuncts shown below: global reflection, injectivity of A_p, and invariance under every group element. The injectivity uses p != 0, proved from phi > 1, so the infinite-dihedral structure does not collapse to a one-point or nonfaithful action.

## References

- Truth anchor: `D5/S3/Analytic/UnitFlow/GaloisReflection.galois_reflection`
