# Roldán's integral circulant energy conjecture

## Abstract

For distinct odd primes p and q, one divisor set uniquely maximises integral circulant energy at order p squared q cubed, including q = 3.

**Definition 1.1 (Integral circulant adjacency).**

$$\forall n \in \mathbb{N},\; \forall D \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall a \in \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(n\right),\; \operatorname{adjacency}\left(n, D, a, b\right) = \operatorname{if} \operatorname{Nat}.\operatorname{gcd}\left(\operatorname{val}\left(a - b\right), n\right) \in D \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3.adjacency` (`✓ std3`).

*Citation.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

Page 1, Section 1: “An integral circulant graph ICG(n, D) has vertex set Z_n and connects a and b whenever gcd(a − b, n) ∈ D, where D is a nonempty set of proper divisors of n.” The indices are Fin n, subtraction is modulo n, and the gcd uses the natural representative of that difference.

**Definition 1.2 (Energy with eigenvalue multiplicity).**

$$\forall n \in \mathbb{N},\; \forall D \in \operatorname{Finset}\left(\mathbb{N}\right),\; \operatorname{energy}\left(n, D\right) = \operatorname{Multiset}.\operatorname{sum}\left(\operatorname{Multiset}.\operatorname{map}\left(\operatorname{fun} x \mapsto |x|, \operatorname{Polynomial}.\operatorname{roots}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{adjacency}\left(n, D\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3.energy` (`✓ std3`).

*Citation.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

Page 1, Section 1: “E(G) = Σ_{i=1}^n |λ_i|, where λ_1, …, λ_n are the eigenvalues of its adjacency matrix.” The multiset roots of the characteristic polynomial retain eigenvalue multiplicity. For an allowed divisor set the adjacency matrix is real symmetric.

**Definition 1.3 (The maximizing divisor set).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{Dstar}\left(p, q\right) = \{1, (p)^{2}, (p) \cdot (q), (q)^{2}, ((p)^{2}) \cdot ((q)^{2}), (p) \cdot ((q)^{3})\}$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3.Dstar` (`✓ std3`).

*Citation.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

Page 3, Conjecture 1.3 uses D* = {1, p^2, pq, q^2, p^2q^2, pq^3}.

**Definition 1.4 (Conjecture 1.3 (Universality)).**

$$claim \Leftrightarrow (\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{Prime}\left(q\right)) \Rightarrow ((\neg (p = q)) \Rightarrow ((\operatorname{Odd}\left(p\right)) \Rightarrow ((\operatorname{Odd}\left(q\right)) \Rightarrow ((\operatorname{Dstar}\left(p, q\right) \subseteq \operatorname{Nat}.\operatorname{properDivisors}\left(((p)^{2}) \cdot ((q)^{3})\right)) \land (\forall D \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\operatorname{Finset}.\operatorname{Nonempty}\left(D\right)) \Rightarrow ((D \subseteq \operatorname{Nat}.\operatorname{properDivisors}\left(((p)^{2}) \cdot ((q)^{3})\right)) \Rightarrow ((\neg (D = \operatorname{Dstar}\left(p, q\right))) \Rightarrow (\operatorname{energy}\left(((p)^{2}) \cdot ((q)^{3}), D\right) < \operatorname{energy}\left(((p)^{2}) \cdot ((q)^{3}), \operatorname{Dstar}\left(p, q\right)\right)))))))))))$$

*Formalization.* `D5/S3/Arith/RoldanCirculantEnergyP2Q3.claim` (`✓ std3`).

*Citation.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

Page 3, Section 1, Conjecture 1.3: “For every pair of distinct odd primes (p, q), the set D* = {1, p^2, pq, q^2, p^2q^2, pq^3} is the unique maximiser of E(p^2q^3, D) over all nonempty D ⊆ div(p^2q^3) ∖ {p^2q^3}.” The first conjunct states that Dstar is allowed; the second gives the strict comparison with every different nonempty allowed divisor set.

**Theorem 1.5 (Ramanujan sums at prime powers).**

$$\forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow (\operatorname{ramanujanSum}\left((p)^{k + 1}, j\right) = (\operatorname{if} (p)^{k + 1} \mid j \operatorname{then} ((p)^{k + 1}: \mathbb{C}) \operatorname{else} 0) - (\operatorname{if} (p)^{k} \mid j \operatorname{then} ((p)^{k}: \mathbb{C}) \operatorname{else} 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RoldanCirculantEnergyP2Q3.ramanujan_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

For a prime p, the Ramanujan sum at p to the power k+1 is the difference of two divisibility indicators, weighted by p to the powers k+1 and k. The values lie in the complex numbers.

**Theorem 1.6 (Ramanujan sum at modulus one).**

$$\forall j \in \mathbb{N},\; \operatorname{ramanujanSum}\left(1, j\right) = (1: \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RoldanCirculantEnergyP2Q3.ramanujan_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

At modulus one the Ramanujan sum equals one for every natural argument.

**Theorem 1.7 (Fourier transform of gcd classes).**

$$\forall n \in \mathbb{N},\; [\operatorname{NeZero}\left(n\right)], \forall D \in \operatorname{Finset}\left(\mathbb{N}\right),\; (D \subseteq \operatorname{Nat}.\operatorname{divisors}\left(n\right)) \Rightarrow (\forall j \in \operatorname{ZMod}\left(n\right),\; \operatorname{ZMod}.\operatorname{dft}\left((\operatorname{fun} (k: \operatorname{ZMod}\left(n\right)) \mapsto ((\operatorname{fun} (k: \operatorname{ZMod}\left(n\right)) \mapsto \operatorname{if} \operatorname{Nat}.\operatorname{gcd}\left(n, \operatorname{val}\left(k\right)\right) \in D \operatorname{then} (1: \mathbb{R}) \operatorname{else} 0)\left(k\right): \mathbb{C})), j\right) = \sum_{d \in D} \operatorname{ramanujanSum}\left(\operatorname{Nat}.\operatorname{div}\left(n, d\right), \operatorname{val}\left(j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RoldanCirculantEnergyP2Q3.gcdRow_dft_ramanujan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

For a nonzero natural n and a finite subset D of its divisors, the Fourier transform of the gcd-class indicator is the sum of the Ramanujan sums at moduli n divided by d. Nat.div denotes natural-number division. The indicator is real-valued and is cast to the complex numbers before applying ZMod.dft.

**Theorem 1.8 (Unique maximization for all distinct odd primes).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{Prime}\left(q\right)) \Rightarrow ((\neg (p = q)) \Rightarrow ((\operatorname{Odd}\left(p\right)) \Rightarrow ((\operatorname{Odd}\left(q\right)) \Rightarrow ((\operatorname{Dstar}\left(p, q\right) \subseteq \operatorname{Nat}.\operatorname{properDivisors}\left(((p)^{2}) \cdot ((q)^{3})\right)) \land (\forall D \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\operatorname{Finset}.\operatorname{Nonempty}\left(D\right)) \Rightarrow ((D \subseteq \operatorname{Nat}.\operatorname{properDivisors}\left(((p)^{2}) \cdot ((q)^{3})\right)) \Rightarrow ((\neg (D = \operatorname{Dstar}\left(p, q\right))) \Rightarrow (\operatorname{energy}\left(((p)^{2}) \cdot ((q)^{3}), D\right) < \operatorname{energy}\left(((p)^{2}) \cdot ((q)^{3}), \operatorname{Dstar}\left(p, q\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RoldanCirculantEnergyP2Q3.result` (`✓ std3`). ∎

*Resolves.* `Problems/roldan-2026-integral-circulant-energy-p2q3` (proved) by `D5/S3/Arith/RoldanCirculantEnergyP2Q3.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"roldan-2026-integral-circulant-energy-p2q3","declaration_gid":"D5/S3/Arith/RoldanCirculantEnergyP2Q3.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. G. Roldán (2026). *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*. DOI: [10.48550/arXiv.2604.09491](https://doi.org/10.48550/arXiv.2604.09491). URL: <https://arxiv.org/abs/2604.09491v1>.

*Commentary.*

Fourier diagonalization expresses the energy as a sum of absolute Ramanujan sums with totient multiplicities. Prime-power divisor coordinates give twelve spectral classes. With u = p − 3 and v = q − 3, replacing each spectral polynomial's coefficients by their absolute values gives a majorant on the nonnegative quadrant. For Dstar the coefficients have one sign in each spectral class, so this majorant is attained. The integer coefficient comparison for every other mask gives an energy deficit of at least 96. The argument permits v = 0 and therefore includes q = 3.

## References

- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.Dstar`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.adjacency`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.claim`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.energy`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.gcdRow_dft_ramanujan`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.ramanujan_one`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.ramanujan_prime_power`
- Truth anchor: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.result`
- Dependency: [D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity](../Analytic/Certified/FiniteRamanujanDivisorIdentity.md)
- Dependency: [D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate](RoldanCirculantEnergyP2Q3Certificate.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration](../ConceptDynamics/Coding/CountedOriginalOrbitGyration.md)
- Dependency: [D5/S3/Quantum/Matrix/CirculantCharpoly](../Quantum/Matrix/CirculantCharpoly.md)
