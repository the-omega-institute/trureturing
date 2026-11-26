# Romik Conjecture 1.3 from the open-range Pfaffian identity

## Abstract

The published open-range cylinder identity determines the rational functions and yields their common regular boundary evaluation.

**Theorem 1.1 (Regularity and common boundary evaluation).**

$$\forall R \in \mathbb{N} \to \operatorname{RatFunc}\left(\mathbb{Q}\right),\; \left(\forall m \in \mathbb{N},\; \forall N \in \mathbb{N},\; \left(1 \le m \land m < N\right) \Rightarrow \operatorname{eval}\left(N, R\left(m\right)\right) = \operatorname{pfaffian}\left(\operatorname{cylinderMatrix}\left(m, N\right)\right)\right) \Rightarrow \left(\forall k \in \mathbb{N},\; 2 \le k \Rightarrow \left(R\left(k\right) = \operatorname{rationalCylinder}\left(k\right) \land \left(R\left(k - 1\right) = \operatorname{rationalCylinder}\left(k - 1\right) \land \left(R\left(k\right) \in \operatorname{regularAt}\left(k\right) \land \left(R\left(k - 1\right) \in \operatorname{regularAt}\left(k\right) \land \left(\operatorname{eval}\left(k, R\left(k\right)\right) = \operatorname{pfaffian}\left(\operatorname{cylinderMatrix}\left(k - 1, k\right)\right) \land \operatorname{eval}\left(k, R\left(k - 1\right)\right) = \operatorname{pfaffian}\left(\operatorname{cylinderMatrix}\left(k - 1, k\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.source_rationalCylinder_boundary` (`✓ std3`). ∎

*Resolves.* `Problems/akyazi-zavadski-2026-romik-conjecture-1-3` (proved) by `D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.source_rationalCylinder_boundary`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akyazi-zavadski-2026-romik-conjecture-1-3","declaration_gid":"D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.source_rationalCylinder_boundary","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melda Akyazi-Zavadski, Nathanaël Berestycki, Sunil Chhita (2026). *On Romik’s rationality conjectures for critical percolation*. URL: <https://arxiv.org/html/2611.26570v1>.

*Commentary.*

Conjecture 1.3, equation (1.2), asks for every integer k≥2 that R_k(k)=R_(k-1)(k). Theorem 1.2, equation (1.1), gives P_C_N(F_m)=R_m(N) for every fixed integer m≥1 and integer N>m. Corollary 4.2, equation (4.4), identifies the same probability with the size-2m Pfaffian of the inverse Kasteleyn matrix on the prescribed endpoints. Equation (5.25) in the proof of Theorem 1.2 identifies that matrix with n=N-1, using the explicit entries of Lemma 4.3, (4.12) and Proposition 5.1. Thus the theorem's sole premise is their published coincidence for every natural m,N with 1≤m<N. That probability-to-Pfaffian bridge is supplied by the paper as an assumption of this formal theorem.

Here R is a family indexed by all natural m with values in RatFunc over the rationals. The premise compares canonical RatFunc.eval, using RingHom.id on the rationals and the rational cast of N, with pfaffian(cylinderMatrix(m,N)). For each natural k≥2 the six conclusions are R(k)=rationalCylinder(k), R(k-1)=rationalCylinder(k-1), membership of R(k) in regularAt(k), membership of R(k-1) in regularAt(k), and the two canonical evaluations at the rational cast of k each equal pfaffian(cylinderMatrix(k-1,k)).

Equality on the infinite integer tail determines a rational function, by deleting the finitely many roots of both reduced denominators and applying the polynomial identity principle to cross-products. Specialization at k gives regularity for the functions of sizes k and k-1. The final unit pair removes the last two endpoints at size k. The two evaluations therefore agree, as conjectured. Equation (2.8) of the cited paper gives the common value 1/A_k, where A_k counts alternating-sign matrices of order k, via the probability of F_(k-1) at circumference 2k. That enumerative identification is a literature consequence outside the formal statement.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree.source_rationalCylinder_boundary`
- Dependency: [D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian](RomikCylinderPfaffian.md)
