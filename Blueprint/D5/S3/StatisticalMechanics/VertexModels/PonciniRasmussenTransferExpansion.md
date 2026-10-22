# The Poncini–Rasmussen transfer expansion

## Abstract

The eight-vertex transfer matrix equals the central factorial polynomial expansion of its principal Hamiltonian over every algebraically closed field of characteristic zero.

**Definition 1.1 (Eight-vertex coefficients).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall u:F, (\forall j:\operatorname{Fin}\left(2\right), (\forall k:\operatorname{Fin}\left(2\right), (\forall l:\operatorname{Fin}\left(2\right), (\forall m:\operatorname{Fin}\left(2\right), (\operatorname{Rcoef}\left(u, j, k, l, m\right) = \operatorname{if} ((j = m) \land (l = k)) \operatorname{then} (1) \operatorname{else} (\operatorname{if} ((j = l) \land ((k = m) \land (j \ne k))) \operatorname{then} (u) \operatorname{else} (\operatorname{if} ((j = k) \land ((l = m) \land (j \ne l))) \operatorname{then} (u) \operatorname{else} (0)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.Rcoef` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 42, (C.15): R^{km}_{jl}(u) is 1 if j = m, l = k; u if j = l, k = m, j ≠ k; u if j = k, l = m, j ≠ l; and 0 otherwise. All four indices belong to Fin 2.

**Definition 1.2 (Boundary coefficients).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall j:\operatorname{Fin}\left(2\right), (\forall k:\operatorname{Fin}\left(2\right), (\operatorname{Kcoef}\left(j, k\right) = \operatorname{if} (j = k) \operatorname{then} (1) \operatorname{else} (0))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.Kcoef` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 42, (C.15): “K^k_j(u) = K̄^k_j(u) = δ_{jk}”. The coefficients are independent of u.

**Definition 1.3 (Two-site operators).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall N:\mathbb{N}, (\forall u:F, (\forall a:\operatorname{Fin}\left(N\right), (\forall b:\operatorname{Fin}\left(N\right), (\operatorname{twoSite}\left(N, u, a, b\right) = \operatorname{fun}(x:\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{fun}(y:\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{if} (\forall c:\operatorname{Fin}\left(N\right), ((c \ne a) \Rightarrow ((c \ne b) \Rightarrow (x\left(c\right) = y\left(c\right))))) \operatorname{then} (\operatorname{Rcoef}\left(u, y\left(a\right), x\left(a\right), y\left(b\right), x\left(b\right)\right)) \operatorname{else} (0))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.twoSite` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 42, (C.9)–(C.10): “R_{i,n+1}(u) := Σ_{j,k,l,m} R^{km}_{jl}(u) 1_{i−1} ⊗ e^k_j ⊗ 1_{n−i} ⊗ e^m_l”. Rows x and columns y are configurations; coordinates outside a and b agree, and the matrix-unit entry is (row, column) = (k, j).

**Definition 1.4 (Boundary operators).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall N:\mathbb{N}, (\forall a:\operatorname{Fin}\left(N\right), (\operatorname{oneSite}\left(N, a\right) = \operatorname{fun}(x:\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{fun}(y:\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{if} (\forall c:\operatorname{Fin}\left(N\right), ((c \ne a) \Rightarrow (x\left(c\right) = y\left(c\right)))) \operatorname{then} (\operatorname{Kcoef}\left(y\left(a\right), x\left(a\right)\right)) \operatorname{else} (0))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.oneSite` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 42, (C.11) defines K_1(u) and K̄_{n+1}(u). The matrix-unit coefficient Kcoef acts on coordinate a, with identity on every other coordinate.

**Definition 1.5 (The ordered double row).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall n:\mathbb{N}, (\forall u:F, (\operatorname{preTrace}\left(n, u\right) = (\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(\operatorname{fun}(i:\operatorname{Fin}\left(n\right)) \mapsto (\operatorname{twoSite}\left(n + 1, u, \operatorname{Fin.castSucc}\left(\operatorname{Fin.rev}\left(i\right)\right), \operatorname{Fin.last}\left(n\right)\right))\right)\right) \cdot \operatorname{oneSite}\left(n + 1, 0\right)) \cdot (\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(\operatorname{fun}(i:\operatorname{Fin}\left(n\right)) \mapsto (\operatorname{twoSite}\left(n + 1, u, \operatorname{Fin.last}\left(n\right), \operatorname{Fin.castSucc}\left(i\right)\right))\right)\right) \cdot \operatorname{oneSite}\left(n + 1, \operatorname{Fin.last}\left(n\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.preTrace` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 42, (C.12): “L_{n+1}(u) := R_{n,n+1}(u) ⋯ R_{1,n+1}(u) K_1(u) R_{n+1,1}(u) ⋯ R_{n+1,n}(u) K̄_{n+1}(u)”. Lean coordinates start at zero and the auxiliary coordinate is Fin.last n.

**Definition 1.6 (The auxiliary partial trace).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall n:\mathbb{N}, (\forall u:F, (\operatorname{transfer}\left(n, u\right) = \operatorname{fun}(x:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{fun}(y:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\sum_{s\in \operatorname{Finset.univ}\left(\operatorname{Fin}\left(2\right)\right)} (\operatorname{preTrace}\left(n, u, \operatorname{Fin.snoc}\left(x, s\right), \operatorname{Fin.snoc}\left(y, s\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.transfer` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 42, (C.13): “Ť_n(u) = Tr_{n+1}(L_{n+1}(u))”. Fin.snoc appends the same auxiliary bit to the row and column, and the sum ranges over its two values.

**Definition 1.7 (The principal Hamiltonian).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] \forall n:\mathbb{N}, (\operatorname{hamiltonian}\left(n\right) = \sum_{i\in \operatorname{Finset.univ}\left(\operatorname{Fin}\left(n\right)\right)} (\operatorname{if}h:\operatorname{Fin.val}\left(i\right) + 1 < n \operatorname{then} (\operatorname{fun}(x:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{fun}(y:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{if} ((\forall c:\operatorname{Fin}\left(n\right), ((c \ne i) \Rightarrow ((c \ne \langle\operatorname{Fin.val}\left(i\right) + 1,h\rangle) \Rightarrow (x\left(c\right) = y\left(c\right))))) \land ((x\left(i\right) \ne y\left(i\right)) \land (x\left(\langle\operatorname{Fin.val}\left(i\right) + 1,h\rangle\right) \ne y\left(\langle\operatorname{Fin.val}\left(i\right) + 1,h\rangle\right)))) \operatorname{then} (1) \operatorname{else} (0)))) \operatorname{else} 0)))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.hamiltonian` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 45, (C.40): “h_n = Σ_{i=1}^{n−1} σ^x_{n,i} σ^x_{n,i+1}”. Each term flips the adjacent pair and fixes every other coordinate. The proof h certifies that the next Fin index belongs to the chain.

**Definition 1.8 (Conjecture C.12).**

$$\operatorname{claim} \Leftrightarrow (\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] [\operatorname{IsAlgClosed}\left(F\right)] [\operatorname{CharZero}\left(F\right)] \forall n:\mathbb{N}, ((1 \le n) \Rightarrow (\forall u:F, (\operatorname{transfer}\left(n, u\right) = ((2:F)) \cdot (\sum_{k\in \operatorname{Finset.range}\left(n\right)} ((\left(1 + u^{2}\right)^{n - k} \cdot \left(2 \cdot u\right)^{k}) \cdot (\sum_{j\in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(k, 2\right) + 1\right)} ((\frac{\operatorname{dfBinom}\left((n:\mathbb{Z}) - (k:\mathbb{Z}) - 2 + 2 \cdot (j:\mathbb{Z}), 2 \cdot (j:\mathbb{Z})\right) \cdot (0 - 1:F)^{j}}{(\operatorname{Nat.factorial}\left(k - 2 \cdot j\right):F)}) \cdot (\operatorname{Polynomial.aeval}\left((\operatorname{hamiltonian}\left(n\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), F\right)), \operatorname{mPoly}\left(k - 2 \cdot j\right)\right)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.claim` (`✓ std3`).

*Citation.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Page 47, Conjecture C.12: “For every n ∈ ℕ and all u ∈ F, we have Ť_n(u) = 2 Σ_{k=0}^{n−1} (1 + u²)^{n−k} (2u)^k Σ_{j=0}^{⌊k/2⌋} [n − k − 2 + 2j over 2j]!! (−1)^j m_{k−2j}(h_n)/(k − 2j)!”. Here n ≥ 1, F is an algebraically closed field of characteristic zero, and the basis of its n-fold tensor power is Fin n → Fin 2. Nat.div denotes natural-number division; natural subtraction is truncated.

**Theorem 1.9 (The transfer expansion).**

$$\forall F:\operatorname{Type}, ([\operatorname{Field}\left(F\right)] [\operatorname{IsAlgClosed}\left(F\right)] [\operatorname{CharZero}\left(F\right)] \forall n:\mathbb{N}, ((1 \le n) \Rightarrow (\forall u:F, (\operatorname{transfer}\left(n, u\right) = ((2:F)) \cdot (\sum_{k\in \operatorname{Finset.range}\left(n\right)} ((\left(1 + u^{2}\right)^{n - k} \cdot \left(2 \cdot u\right)^{k}) \cdot (\sum_{j\in \operatorname{Finset.range}\left(\operatorname{Nat.div}\left(k, 2\right) + 1\right)} ((\frac{\operatorname{dfBinom}\left((n:\mathbb{Z}) - (k:\mathbb{Z}) - 2 + 2 \cdot (j:\mathbb{Z}), 2 \cdot (j:\mathbb{Z})\right) \cdot (0 - 1:F)^{j}}{(\operatorname{Nat.factorial}\left(k - 2 \cdot j\right):F)}) \cdot (\operatorname{Polynomial.aeval}\left((\operatorname{hamiltonian}\left(n\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), F\right)), \operatorname{mPoly}\left(k - 2 \cdot j\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Poncini and Jørgen Rasmussen (2023). *Integrability of planar-algebraic models*. DOI: [10.1088/1742-5468/acdce7](https://doi.org/10.1088/1742-5468/acdce7). URL: <https://arxiv.org/abs/2206.14462v2>.

*Commentary.*

Conjecture C.12 holds. The ordered product reduces to commuting adjacent flips, whose Walsh eigenvectors have Hamiltonian eigenvalue n − 1 − 2l. The scalar central factorial identity then gives the matrix equality.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.Kcoef`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.Rcoef`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.hamiltonian`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.oneSite`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.preTrace`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.result`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion.twoSite`
- Dependency: [D5/S1/Recurrence/CentralFactorialTransferExpansion](../../../S1/Recurrence/CentralFactorialTransferExpansion.md)
- Dependency: [D5/S3/Analytic/Hunter/NCHunterPositivity](../../Analytic/Hunter/NCHunterPositivity.md)
- Dependency: [D5/S3/Estimation/DataProcessing/OneCutZeroExcess](../../Estimation/DataProcessing/OneCutZeroExcess.md)
