# Ikhlef–Morin-Duchesne seed products

## Abstract

Uniform product evaluations of the periodic Temperley–Lieb seed recurrences.

**Definition 1.1 (The q-number).**

$$\forall q: \mathbb{C}, \forall k: \mathbb{Z}, \operatorname{qbr}\left(q, k\right) = \frac{q^{k} - q^{-k}}{q - q^{-1}}$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.qbr` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Equation (2.14), p. 11, writes [k] = (q^k − q^{−k})/(q − q^{−1}). Here k is an integer and q is complex; all divisions are complex divisions.

**Definition 1.2 (The symmetric q-power).**

$$\forall q: \mathbb{C}, \forall k: \mathbb{Z}, \operatorname{qcb}\left(q, k\right) = q^{k} + q^{-k}$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.qcb` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Proposition C.1 (p. 61): "where α_p = q^p + q^{−p} and {m} = q^m + q^{−m}." The argument k ranges over the integers.

**Definition 1.3 (A variable and its inverse).**

$$\forall z: \mathbb{C}, \operatorname{al}\left(z\right) = z + z^{-1}$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.al` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Proposition C.1 (p. 61): "where X^{(p)}_m(ω, x, y) is a polynomial in the variables α_a = x + x^{−1}, α_b = y + y^{−1} and α_ω = ω + ω^{−1}, that satisfies the recursion relation for m ⩾ p + 1". The function al sends z to z + z⁻¹.

**Definition 1.4 (The positive-depth seed recurrence).**

$$\forall q: \mathbb{C}, \forall x: \mathbb{C}, \forall y: \mathbb{C}, \forall w: \mathbb{C}, \forall p: \mathbb{N}, (\operatorname{seedX}\left(q, x, y, w, p, 0\right) = 1) \land ((\operatorname{seedX}\left(q, x, y, w, p, 1\right) = \operatorname{al}\left(x\right) + \frac{\operatorname{al}\left(y\right) \cdot \operatorname{al}\left(w\right)}{\operatorname{qcb}\left(q, \operatorname{Int}.\operatorname{ofNat}(p) + 1\right)}) \land (\forall n: \mathbb{N}, \operatorname{let} k: \mathbb{Z} := \operatorname{Int}.\operatorname{ofNat}(p) + \operatorname{Int}.\operatorname{ofNat}(n) + 1; \operatorname{seedX}\left(q, x, y, w, p, n + 2\right) = (\operatorname{al}\left(x\right) + \frac{\operatorname{al}\left(q^{p}\right) \cdot \operatorname{al}\left(y\right) \cdot \operatorname{al}\left(w\right)}{\operatorname{qcb}\left(q, k\right) \cdot \operatorname{qcb}\left(q, k + 1\right)}) \cdot \operatorname{seedX}\left(q, x, y, w, p, n + 1\right) + \frac{(\operatorname{al}\left(q^{p}\right)^{2} - \operatorname{qcb}\left(q, k\right)^{2}) \cdot (\operatorname{al}\left(y\right)^{2} - \operatorname{qcb}\left(q, k\right)^{2}) \cdot (\operatorname{al}\left(w\right)^{2} - \operatorname{qcb}\left(q, k\right)^{2})}{(q - q^{-1})^{2} \cdot \operatorname{qbr}\left(q, 2 \cdot k - 1\right) \cdot \operatorname{qbr}\left(q, 2 \cdot k + 1\right) \cdot \operatorname{qcb}\left(q, k\right)^{2}} \cdot \operatorname{seedX}\left(q, x, y, w, p, n\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.seedX` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Proposition C.1 (p. 61): "where X^{(p)}_m(ω, x, y) is a polynomial in the variables α_a = x + x^{−1}, α_b = y + y^{−1} and α_ω = ω + ω^{−1}, that satisfies the recursion relation for m ⩾ p + 1". Equations (C.3)–(C.4) give X_{m+1} = (α_a + α_pα_bα_ω/({m}{m+1})) X_m + (α_p² − {m}²)(α_b² − {m}²)(α_ω² − {m}²)/((q − q⁻¹)²[2m − 1][2m + 1]{m}²) X_{m−1}, with X_p = 1 and X_{p+1} = α_a + α_bα_ω/{p + 1}. The expression seedX q x y w p n denotes X^{(p)}_{p+n}(w,x,y). The recurrence index is k = p+n+1; Int.ofNat displays each natural-to-integer coercion.

**Definition 1.5 (The zero-depth seed recurrence).**

$$\forall q: \mathbb{C}, \forall x: \mathbb{C}, \forall y: \mathbb{C}, \forall w: \mathbb{C}, (\operatorname{seedSigma}\left(q, x, y, w, 0\right) = 1) \land ((\operatorname{seedSigma}\left(q, x, y, w, 1\right) = \operatorname{al}\left(x\right) + \frac{\operatorname{al}\left(y\right) \cdot \operatorname{al}\left(w\right)}{\operatorname{qcb}\left(q, 1\right)}) \land (\forall n: \mathbb{N}, \operatorname{let} k: \mathbb{Z} := \operatorname{Int}.\operatorname{ofNat}(n) + 1; \operatorname{seedSigma}\left(q, x, y, w, n + 2\right) = (\operatorname{al}\left(x\right) + \frac{2 \cdot \operatorname{al}\left(y\right) \cdot \operatorname{al}\left(w\right)}{\operatorname{qcb}\left(q, k\right) \cdot \operatorname{qcb}\left(q, k + 1\right)}) \cdot \operatorname{seedSigma}\left(q, x, y, w, n + 1\right) - \frac{\operatorname{qbr}\left(q, k\right)^{2} \cdot (\operatorname{al}\left(y\right)^{2} - \operatorname{qcb}\left(q, k\right)^{2}) \cdot (\operatorname{al}\left(w\right)^{2} - \operatorname{qcb}\left(q, k\right)^{2})}{\operatorname{qbr}\left(q, 2 \cdot k + 1\right) \cdot \operatorname{qbr}\left(q, 2 \cdot k - 1\right) \cdot \operatorname{qcb}\left(q, k\right)^{2}} \cdot \operatorname{seedSigma}\left(q, x, y, w, n\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.seedSigma` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Proposition C.2 (p. 65): "The seed states σ^{(0)}_{0,m} with m ⩾ 0 are polynomials in α_a = x + x^{−1}, α_b = y + y^{−1} and α_{ab} = w + w^{−1} that satisfy the linear system for m ⩾ 1". Equations (C.24)–(C.25) give the displayed recurrence and its two initial values, independently of seedX.

**Definition 1.6 (The symmetric finite product).**

$$\forall q: \mathbb{C}, \forall x: \mathbb{C}, \forall w: \mathbb{C}, \forall epsilon: \mathbb{C}, \forall N: \mathbb{N}, \operatorname{seedProduct}\left(q, x, w, epsilon, N\right) = (w \cdot x)^{-\operatorname{Int}.\operatorname{ofNat}(N)} \cdot \prod_{j \in \operatorname{Finset}.\operatorname{range}(N)} ((x \cdot q^{-\operatorname{Int}.\operatorname{ofNat}(N) + 1 + 2 \cdot \operatorname{Int}.\operatorname{ofNat}(j)} + epsilon \cdot w) \cdot (epsilon \cdot q^{-\operatorname{Int}.\operatorname{ofNat}(N) + 1 + 2 \cdot \operatorname{Int}.\operatorname{ofNat}(j)} + x \cdot w))$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.seedProduct` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Conjecture C.1 (p. 62): "For p ⩾ 1, the function X^{(p)}_m(ω, x, y) specialised to y = εq^m evaluates to X^{(p)}_m(ω, x, εq^m) = (ωx)^{p−m} ∏_{r=−(m−p−1)/2}^{(m−p−1)/2} (xq^{2r} + εω)(εq^{2r} + xω). (C.5)" The product has N factors, with integer exponent 2r = −N+1+2j for j in Finset.range N. For N=0 the product is empty and equals one. The same expression occurs in (C.26).

**Definition 1.7 (Conjectures C.1 and C.2).**

$$claim = (\forall q: \mathbb{C}, \forall x: \mathbb{C}, \forall w: \mathbb{C}, \forall epsilon: \mathbb{C}, (q \neq 0) \implies ((x \neq 0) \implies ((w \neq 0) \implies ((\forall n: \mathbb{N}, (1 \leq n) \implies (q^{n} \neq 1)) \implies ((epsilon = 1 \lor epsilon = -1) \implies ((\forall p: \mathbb{N}, \forall m: \mathbb{N}, (1 \leq p) \implies ((p \leq m) \implies (\operatorname{seedX}\left(q, x, epsilon \cdot q^{m}, w, p, m - p\right) = \operatorname{seedProduct}\left(q, x, w, epsilon, m - p\right)))) \land (\forall m: \mathbb{N}, \operatorname{seedSigma}\left(q, x, epsilon \cdot q^{m}, w, m\right) = \operatorname{seedProduct}\left(q, x, w, epsilon, m\right))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.claim` (`✓ std3`).

*Citation.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

Conjecture C.1 (p. 62): "For p ⩾ 1, the function X^{(p)}_m(ω, x, y) specialised to y = εq^m evaluates to X^{(p)}_m(ω, x, εq^m) = (ωx)^{p−m} ∏_{r=−(m−p−1)/2}^{(m−p−1)/2} (xq^{2r} + εω)(εq^{2r} + xω). (C.5)" Conjecture C.2 (p. 65): "The intermediate seed states σ^{(0)}_{0,m}(w, x, y) specialised to y = εq^m evaluate to σ^{(0)}_{0,m}(w, x, εq^m) = (wx)^{−m} ∏_{r=−(m−1)/2}^{(m−1)/2} (xq^{2r} + εw)(εq^{2r} + xw). (C.26)" The domain is nonzero complex q,x,w, with q not a root of unity and ε equal to 1 or −1. The first assertion has 1 ≤ p ≤ m; the second has every natural m. Natural subtraction m−p is truncated subtraction, and agrees with the integer difference under p ≤ m.

**Theorem 1.8 (Both product formulas hold).**

$$\forall q: \mathbb{C}, \forall x: \mathbb{C}, \forall w: \mathbb{C}, \forall epsilon: \mathbb{C}, (q \neq 0) \implies ((x \neq 0) \implies ((w \neq 0) \implies ((\forall n: \mathbb{N}, (1 \leq n) \implies (q^{n} \neq 1)) \implies ((epsilon = 1 \lor epsilon = -1) \implies ((\forall p: \mathbb{N}, \forall m: \mathbb{N}, (1 \leq p) \implies ((p \leq m) \implies (\operatorname{seedX}\left(q, x, epsilon \cdot q^{m}, w, p, m - p\right) = \operatorname{seedProduct}\left(q, x, w, epsilon, m - p\right)))) \land (\forall m: \mathbb{N}, \operatorname{seedSigma}\left(q, x, epsilon \cdot q^{m}, w, m\right) = \operatorname{seedProduct}\left(q, x, w, epsilon, m\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yacine Ikhlef and Alexi Morin-Duchesne (2024). *Fusion of irreducible modules in the periodic Temperley–Lieb algebra*. DOI: [10.21468/SciPostPhys.17.5.132](https://doi.org/10.21468/SciPostPhys.17.5.132). URL: <https://arxiv.org/abs/2312.14837v2>.

*Commentary.*

The seed recurrence equals a monic Askey–Wilson recurrence after Q=q², h=q^(p+1), a=h/(yw), b=hw/y, c=hyw, d=hy/w, and T=−al(x). A coupled Darboux identity shifts a to aQ. At the terminal degree the coefficient A vanishes because abQ^(N−1)=1. Induction then gives one linear factor at each shift. Symmetric exponents sum to zero, producing seedProduct. The separately defined sigma recurrence equals the p=0 seedX recurrence. The formulas hold uniformly in m and p; intermediate values at a fixed specialization are not asserted to factor.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.al`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.qbr`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.qcb`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.result`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.seedProduct`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.seedSigma`
- Truth anchor: `D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.seedX`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry](../../FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry.md)
