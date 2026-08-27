# Galois Reflection of the Golden Unit Flow

## Abstract

Galois conjugation reflects the Golden unit-flow principal zeta and completes its regulator periodicity to a faithful infinite-dihedral symmetry.

**Theorem 1.1 (Galois reflection and infinite-dihedral invariance).**

$$p = 2 \log(\varphi),\\\forall K, NumberField(K), \forall sigmaPlus, sigmaMinus \in Emb(K, \mathbb{R}), \forall tau \in AutQ(K), \forall s \in \mathbb{C},\\{}[\forall alpha \in RingOfIntegers(K), a(tau(alpha)) = b(alpha) \land b(tau(alpha)) = a(alpha)] \land\\1 < \Re(s) \land Periodic(Zs, p)\\\longrightarrow\\{}[\forall eta \in \mathbb{R}, Zs(eta) = Zs(-eta)] \land\\\operatorname{Injective}(Ap: DihedralGroup(0) \to Perm(\mathbb{R})) \land\\{}[\forall g \in DihedralGroup(0), \forall eta \in \mathbb{R}, Zs(Ap(g)(eta)) = Zs(eta)].$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/UnitFlow/GaloisReflection.galois_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a number field with real embeddings sigmaPlus and sigmaMinus, and let tau be the Q-algebra automorphism giving Galois conjugation. For a nonzero algebraic integer alpha, the Lean definitions set a(alpha) = |sigmaPlus(alpha)|^2, b(alpha) = |sigmaMinus(alpha)|^2, Q_eta(alpha) = exp(eta)a(alpha) + exp(-eta)b(alpha), and define Z_s(eta) as the complex-power tsum of Q_eta(alpha)^(-s) over the actual subtype of nonzero elements of the ring of integers.

The hypotheses shown in the formula are exactly the public Lean premises: the two a/b exchange equations, Re(s) > 1 from the source domain, and period p = 2 log(phi) from the immediately preceding regulator theorem. Restricting tau with Mathlib's RingOfIntegers.mapAlgEquiv gives an equivalence of the nonzero summation index, and Equiv.tsum_eq reindexes the series after Q_eta(tau(alpha)) = Q_(-eta)(alpha).

Here A_p is the displayed Lean monoid homomorphism from Mathlib's DihedralGroup 0 to permutations of the real parameter line: A_p(r_k)(eta) = eta + k p and A_p(sr_k)(eta) = -eta - k p. The theorem concludes all three conjuncts shown below: global reflection, injectivity of A_p, and invariance under every group element. The injectivity uses p != 0, proved from phi > 1, so the infinite-dihedral structure does not collapse to a one-point or nonfaithful action.

## References

- Truth anchor: `D5/S3/Analytic/UnitFlow/GaloisReflection.galois_reflection`
