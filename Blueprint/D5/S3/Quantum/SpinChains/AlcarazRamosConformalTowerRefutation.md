# The lowest-mode Alcaraz–Ramos prediction fails

## Abstract

The homogeneous N=3 lowest quasienergy cannot have the predicted conformal limit.

**Definition 1.1 (The polynomial recurrence).**

$$((\operatorname{poly}\left(0\right) = 1) \land ((\operatorname{poly}\left(1\right) = 1) \land (\operatorname{poly}\left(2\right) = 1))) \land (\forall n \in \mathbb{N},\; \operatorname{poly}\left(n + 3\right) = \operatorname{poly}\left(n + 2\right) - \operatorname{Polynomial}.\operatorname{X} \cdot \operatorname{poly}\left(n\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.poly` (`✓ std3`).

*Citation.* Francisco C. Alcaraz, Lucas M. Ramos (2024). *Conformally invariant free parafermionic quantum chains with multispin interactions*. DOI: [10.1103/PhysRevE.109.044138](https://doi.org/10.1103/PhysRevE.109.044138). URL: <https://arxiv.org/abs/2402.09936v3>.

*Commentary.*

Page 4, Eqs. (26)–(27): “P_M^{(N)}(z) = P_{M−1}^{(N)}(z) − zλ_M^N P_{M−N}^{(N)}(z),” followed by “with the initial condition” and “P_M^{(N)}(z) = 1, for M ≤ 0,”. Here N=3, λ_j=1, and poly(n)=P_{n−2}; the three initial indices represent nonpositive M. Polynomial.X is the polynomial indeterminate.

**Definition 1.2 (Nonnegative lattice sizes).**

$$\forall M \in \mathbb{N},\; \operatorname{P}\left(M\right) = \operatorname{poly}\left(M + 2\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.P` (`✓ std3`).

*Citation.* Francisco C. Alcaraz, Lucas M. Ramos (2024). *Conformally invariant free parafermionic quantum chains with multispin interactions*. DOI: [10.1103/PhysRevE.109.044138](https://doi.org/10.1103/PhysRevE.109.044138). URL: <https://arxiv.org/abs/2402.09936v3>.

*Commentary.*

Page 4, Eq. (26): “P_M^{(N)}(z) = P_{M−1}^{(N)}(z) − zλ_M^N P_{M−N}^{(N)}(z),”. P(M) is P_M^{(3)} at homogeneous couplings λ_j=1, expressed through poly with its index shifted by two. Thus P(0)=1.

**Definition 1.3 (Ordered positive-root quasienergies).**

$$\forall M \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{quasienergy}\left(M, i\right) = (\operatorname{List}.\operatorname{getD}\left(\operatorname{Multiset}.\operatorname{sort}\left(((a : \mathbb{R}) \mapsto ((b : \mathbb{R}) \mapsto a \ge b)), \operatorname{Multiset}.\operatorname{filter}\left(((z : \mathbb{R}) \mapsto 0 < z), (\operatorname{P}\left(M\right)).\operatorname{roots}\right)\right), (i - 1), 0\right))^{-\frac{1}{3}}$$

*Formalization.* `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.quasienergy` (`✓ std3`).

*Citation.* Francisco C. Alcaraz, Lucas M. Ramos (2024). *Conformally invariant free parafermionic quantum chains with multispin interactions*. DOI: [10.1103/PhysRevE.109.044138](https://doi.org/10.1103/PhysRevE.109.044138). URL: <https://arxiv.org/abs/2402.09936v3>.

*Commentary.*

Page 4, immediately before Eq. (26): “Apart from the zero modes they are given by Λ_k = 1/z_k^{1/N}, where z_k are the roots (P_M^{(N)}(z_k)=0) of the characteristic polynomial”. Eq. (38), pages 5–6, orders the quasienergies by i=1,2,… . Positive real roots are sorted in decreasing order with multiplicity. The index i−1 uses natural subtraction, truncated at zero. List.getD supplies zero when the index is absent. The outer power is Real.rpow, so the exponent is the real number −1/3.

**Definition 1.4 (The fixed-index leading prediction).**

$$\operatorname{claim} = (\forall i \in \mathbb{N},\; (1 \le i) \Rightarrow (\operatorname{Tendsto}\left(((m : \mathbb{N}) \mapsto (3 \cdot m : \mathbb{R}) \cdot \operatorname{quasienergy}\left((3 \cdot m), i\right)), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{Real}.\operatorname{pi} \cdot (2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(3\right)) \cdot (\frac{7}{6} + (i : \mathbb{R}) - 1)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.claim` (`✓ std3`).

*Citation.* Francisco C. Alcaraz, Lucas M. Ramos (2024). *Conformally invariant free parafermionic quantum chains with multispin interactions*. DOI: [10.1103/PhysRevE.109.044138](https://doi.org/10.1103/PhysRevE.109.044138). URL: <https://arxiv.org/abs/2402.09936v3>.

*Commentary.*

Page 5, Eq. (38), continuing on page 6: “1/z_i^{1/N} = ε_i = π A_i^{(N)}/M = π A^{(N)}/M (x_s^{(N)} + i − 1),” and “for i = 1, 2, …”. Page 6: “Our numerical solutions for polynomial roots with M up to 10⁹ corroborate the conformal invariance prediction (38) for the roots. We conjecture the following exact values for N = 2, 3, 4 and 6”. Eqs. (39) and (41) include “A^{(3)} = 2√3” and “x_s^{(3)} = 7/6 (mod(M,3)=0)”. The leading behaviour is expressed as Tendsto along M=3m for every fixed natural i≥1. The coefficients involving i are real; the lattice-size multiplication 3*m is natural before its cast to ℝ. The TeX labels (4.7), (4.8), (4.10) correspond to printed Eqs. (38), (39), (41).

**Theorem 1.5 (Refutation at the lowest mode).**

$$\neg (\forall i \in \mathbb{N},\; (1 \le i) \Rightarrow (\operatorname{Tendsto}\left(((m : \mathbb{N}) \mapsto (3 \cdot m : \mathbb{R}) \cdot \operatorname{quasienergy}\left((3 \cdot m), i\right)), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{Real}.\operatorname{pi} \cdot (2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(3\right)) \cdot (\frac{7}{6} + (i : \mathbb{R}) - 1)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Francisco C. Alcaraz, Lucas M. Ramos (2024). *Conformally invariant free parafermionic quantum chains with multispin interactions*. DOI: [10.1103/PhysRevE.109.044138](https://doi.org/10.1103/PhysRevE.109.044138). URL: <https://arxiv.org/abs/2402.09936v3>.

*Commentary.*

It suffices to use i=1. The recurrence gives the coefficient formula (−1)^j choose(n−2j,j). Reversing the finite sum at M=3m gives a scaled polynomial Q_m. Binomial asymptotics and dominated convergence imply Q_m(v_m) → F(u) whenever v_m → u and eventually |v_m|≤5, where F(u)=Σ_{k≥0}(−1)^k u^{3k}/(3k+2)!. The alternating-series lower bound through k=5 proves F(u)>0 throughout [4.2321,4.2323]. Bounds on π and √3 place 7π/(3√3) in that interval. The predicted quasienergy limit would produce positive roots with Q_m(v_m)=0 eventually, forcing F(7π/(3√3))=0, a contradiction. The argument does not establish existence or the exact value of the actual lowest-mode limit, equal spacing of its first zeros, other N or residue classes, or asymptotic large-index spacing.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.P`
- Truth anchor: `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.poly`
- Truth anchor: `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.quasienergy`
- Truth anchor: `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.result`
