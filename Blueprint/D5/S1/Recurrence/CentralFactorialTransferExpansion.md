# Central factorial transfer coefficients

## Abstract

Central factorial polynomials expand the binary spectral polynomial and its homogenized transfer eigenvalue over a field of characteristic zero.

**Definition 1.1 (Central factorial polynomials).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall j:\mathbb{N}, (\operatorname{mPoly}\left(j\right) = \prod_{k\in \operatorname{Finset.range}\left(j\right)} (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((j:F) - 1 - 2 \cdot (k:F)\right))))$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialTransferExpansion.mPoly` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 45, (C.44): “m_j(x) := Π_{k=0}^{j−1} [x − (j − 1 − 2k)], j ∈ ℕ.” The product is a Polynomial over F; the empty product is one.

**Definition 1.2 (Double factorial binomial coefficients).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall a:\mathbb{Z}, (\forall b:\mathbb{Z}, (\operatorname{dfBinom}\left(a, b\right) = \frac{(\operatorname{Nat.doubleFactorial}\left(\operatorname{Int.toNat}\left(a\right)\right):F)}{(\operatorname{Nat.doubleFactorial}\left(\operatorname{Int.toNat}\left(b\right)\right):F) \cdot (\operatorname{Nat.doubleFactorial}\left(\operatorname{Int.toNat}\left(a - b\right)\right):F)})))$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialTransferExpansion.dfBinom` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 47, (C.65): “n_1!!/(n_2!!(n_1 − n_2)!!).” The integer arguments are sent through Int.toNat before Nat.doubleFactorial, so (−1)!! = 0!! = 1. Division is field division.

**Definition 1.3 (Transfer eigenvalues).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall m:\mathbb{N}, (\forall l:\mathbb{N}, (\forall u:F, (\operatorname{scalarEigenvalue}\left(m, l, u\right) = 2 \cdot \left(1 + u^{2}\right) \cdot \left(1 - u\right)^{2 \cdot l} \cdot \left(1 + u\right)^{2 \cdot \left(m - l\right)}))))$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialTransferExpansion.scalarEigenvalue` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 45, (C.46): “λ_k(u) = 2(1 + u²)(1 − u)^(2k)(1 + u)^(2(n − 1 − k))”. Here m = n − 1 counts internal edges and l = k counts sign changes. Natural subtraction is truncated.

**Definition 1.4 (Scalar central factorial expansion).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall m:\mathbb{N}, (\forall l:\mathbb{N}, (\forall u:F, (\operatorname{scalarExpansion}\left(m, l, u\right) = 2 \cdot \sum_{k\in \operatorname{Finset.range}\left(m + 1\right)} (\left(1 + u^{2}\right)^{m + 1 - k} \cdot \left(2 \cdot u\right)^{k} \cdot \sum_{j\in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(k, 2\right) + 1\right)} (\frac{\operatorname{dfBinom}\left((m + 1:\mathbb{Z}) - (k:\mathbb{Z}) - 2 + 2 \cdot (j:\mathbb{Z}), 2 \cdot (j:\mathbb{Z})\right) \cdot (0 - 1:F)^{j}}{(\operatorname{Nat.factorial}\left(k - 2 \cdot j\right):F)} \cdot \operatorname{Polynomial.eval}\left((m:F) - 2 \cdot (l:F), \operatorname{mPoly}\left(k - 2 \cdot j\right)\right)))))))$$

*Formalization.* `D5/S1/Recurrence/CentralFactorialTransferExpansion.scalarExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The right side evaluates the central factorial polynomials at m − 2l. Nat.div k 2 is natural-number division; subtraction within natural indices is truncated. Polynomial.eval is written with its evaluation point first.

**Theorem 1.5 (The central factorial coefficient identity).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] [\operatorname{CharZero}\left(F\right)] \forall m:\mathbb{N}, (\forall l:\mathbb{N}, (\forall k:\mathbb{N}, ((l \le m) \Rightarrow ((k \le m) \Rightarrow (\operatorname{PowerSeries.coeff}\left(k, \left(1 + (\operatorname{PowerSeries.X}:\operatorname{PowerSeries}\left(F\right))\right)^{m - l} \cdot \left(1 - \operatorname{PowerSeries.X}\right)^{l}\right) = \sum_{j\in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(k, 2\right) + 1\right)} (\frac{\operatorname{dfBinom}\left((m + 1:\mathbb{Z}) - (k:\mathbb{Z}) - 2 + 2 \cdot (j:\mathbb{Z}), 2 \cdot (j:\mathbb{Z})\right) \cdot (0 - 1:F)^{j}}{(\operatorname{Nat.factorial}\left(k - 2 \cdot j\right):F)} \cdot \operatorname{Polynomial.eval}\left((m:F) - 2 \cdot (l:F), \operatorname{mPoly}\left(k - 2 \cdot j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialTransferExpansion.central_spectral_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The coefficient of the binary spectral polynomial is the finite double factorial sum. Formal series substitution and a second-order recurrence give the identity; no convergence hypothesis is needed.

**Theorem 1.6 (The scalar transfer identity).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] [\operatorname{CharZero}\left(F\right)] \forall m:\mathbb{N}, (\forall l:\mathbb{N}, ((l \le m) \Rightarrow (\forall u:F, (\operatorname{scalarEigenvalue}\left(m, l, u\right) = \operatorname{scalarExpansion}\left(m, l, u\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CentralFactorialTransferExpansion.scalar_settlement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

The coefficient identity is homogenized at 2u/(1 + u²); the case 1 + u² = 0 is treated directly. The equality holds over every field of characteristic zero.

## References

- Truth anchor: `D5/S1/Recurrence/CentralFactorialTransferExpansion.central_spectral_coeff`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialTransferExpansion.dfBinom`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialTransferExpansion.mPoly`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialTransferExpansion.scalarEigenvalue`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialTransferExpansion.scalarExpansion`
- Truth anchor: `D5/S1/Recurrence/CentralFactorialTransferExpansion.scalar_settlement`
