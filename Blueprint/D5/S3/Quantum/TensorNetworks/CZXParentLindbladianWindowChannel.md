# CZX parent-Lindbladian window channel

## Abstract

The CZX parent-Lindbladian window channel and its gauge calculus.

**Definition 1.1 (The two-site change of basis).**

$$\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxU} = \begin{pmatrix}1&0&0&0\\0&0&0&1\\0&1&0&0\\0&0&1&0\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.czxU` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The 4 by 4 permutation matrix is the two-site change of basis displayed in Appendix F, with the computational basis in source order (main.tex l. 4858–4863).

**Definition 1.2 (The signed four-site permutation).**

$$\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxV} = \lambda (r: \operatorname{Fin}\left(16\right)) \mapsto (\lambda (c: \operatorname{Fin}\left(16\right)) \mapsto (\operatorname{ite}\left((r, c) \in \{(0, 0), (1, 15), (2, 2), (3, 13), (4, 4), (5, 11), (6, 6), (8, 1), (9, 14), (10, 3), (12, 5), (13, 10), (14, 7), (15, 8)\}, (1: \mathbb{C}), \operatorname{ite}\left((r, c) = (7, 9) \lor (r, c) = (11, 12), -(1: \mathbb{C}), (0: \mathbb{C})\right)\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.czxV` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The 16 by 16 signed permutation has the fourteen positive entries and two negative entries listed in Appendix F (main.tex l. 4933–4937). Its row and column indices are the four-bit window words.

**Definition 1.3 (The two-site block weight).**

$$\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{mu} = \frac{\operatorname{Real}.{sqrt}\left(3\right)}{4}$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.mu` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The common block weight is the positive real number square root of three divided by four (main.tex l. 4870).

**Definition 1.4 (The four-site block weight).**

$$\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{nu} = \frac{\operatorname{Real}.{sqrt}\left(3\right)}{16}$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.nu` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The multiplicity block weight is square root of three divided by sixteen (main.tex l. 4930).

**Definition 1.5 (The four-to-two renormalization channel).**

$$\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{renormS}\left(x\right) = ((\operatorname{Matrix}.{conjTranspose}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxU}\right)) \cdot (\operatorname{Matrix}.{of}\left(\lambda (r: \operatorname{Fin}\left(4\right)) \mapsto (\lambda (s: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{ite}\left(\operatorname{Fin}.{divNat}\left(2, 2, r\right) = \operatorname{Fin}.{divNat}\left(2, 2, s\right), \sum_{m: \operatorname{Fin}\left(4\right)} \left(((\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxV}) \cdot (x)) \cdot (\operatorname{Matrix}.{conjTranspose}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxV}\right))\right)\left(\operatorname{Fin}.{mk}\left((((8) \cdot (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{divNat}\left(2, 2, r\right)\right))) + ((2) \cdot (\operatorname{Fin}.{val}\left(m\right)))) + (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{modNat}\left(2, 2, r\right)\right))\right), \operatorname{Fin}.{mk}\left((((8) \cdot (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{divNat}\left(2, 2, s\right)\right))) + ((2) \cdot (\operatorname{Fin}.{val}\left(m\right)))) + (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{modNat}\left(2, 2, s\right)\right))\right)\right), (0: \mathbb{C})\right)))\right))) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxU})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.renormS` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

RenormS conjugates by the signed permutation and the two-site basis change, pinches equal sector labels, and sums the four-dimensional multiplicity index, matching the source's S channel (main.tex l. 3149–3164). Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.

**Definition 1.6 (The two-to-four renormalization channel).**

$$\forall (y: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{renormT}\left(y\right) = ((\operatorname{Matrix}.{conjTranspose}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxV}\right)) \cdot (\operatorname{Matrix}.{of}\left(\lambda (r: \operatorname{Fin}\left(16\right)) \mapsto (\lambda (s: \operatorname{Fin}\left(16\right)) \mapsto (\operatorname{ite}\left(\operatorname{Fin}.{divNat}\left(2, 8, r\right) = \operatorname{Fin}.{divNat}\left(2, 8, s\right), (((\frac{\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{nu}}{\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{mu}}: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right))\left(\operatorname{Function}.{comp}\left(\operatorname{Fin}.{divNat}\left(4, 2\right), \operatorname{Fin}.{modNat}\left(2, 8\right), r\right), \operatorname{Function}.{comp}\left(\operatorname{Fin}.{divNat}\left(4, 2\right), \operatorname{Fin}.{modNat}\left(2, 8\right), s\right)\right))) \cdot (\left(((\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxU}) \cdot (y)) \cdot (\operatorname{Matrix}.{conjTranspose}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxU}\right))\right)\left(\operatorname{Fin}.{mk}\left(((2) \cdot (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{divNat}\left(2, 8, r\right)\right))) + (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{modNat}\left(8, 2, r\right)\right))\right), \operatorname{Fin}.{mk}\left(((2) \cdot (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{divNat}\left(2, 8, s\right)\right))) + (\operatorname{Fin}.{val}\left(\operatorname{Fin}.{modNat}\left(8, 2, s\right)\right))\right)\right)), (0: \mathbb{C})\right)))\right))) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxV})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.renormT` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

RenormT conjugates by the signed permutation, inserts the normalized multiplicity identity with scalar nu divided by mu, and restores the source tensor order, matching the source's T channel (main.tex l. 3132–3147). The source multiplicity trace satisfies m_lambda = mu_lambda, so the common weight mu is used directly. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.

**Definition 1.7 (The four-site channel).**

$$\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(16\right), \operatorname{Fin}\left(16\right), \mathbb{C}\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{localChannel}\left(x\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{renormT}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{renormS}\left(x\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.localChannel` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The local channel applies the four-to-two channel S, then the two-to-four channel T, as in the source's E = T composed with S (main.tex l. 4951–4952).

**Definition 1.8 (Cyclic site displacement).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (k: \mathbb{N}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, k\right) = \operatorname{Fin}.{mk}\left(\operatorname{Nat}.{mod}\left((\operatorname{Fin}.{val}\left(i\right)) + (k), n\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.site` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Site i k is the cyclic displacement of i by the natural offset k. The result is represented by the residue modulo n. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.

**Definition 1.9 (The four-bit window code).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowCode}\left(i, x\right) = \operatorname{Fin}.{mk}\left(((((8) \cdot (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 0\right)\right)\right))) + ((4) \cdot (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 1\right)\right)\right)))) + ((2) \cdot (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 2\right)\right)\right)))) + (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 3\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowCode` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

WindowCode reads four consecutive cyclic bits, with the first site as the most significant bit, and packs them into Fin 16. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.

**Definition 1.10 (Writing a window word).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (p: \operatorname{Fin}\left(16\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowUpdate}\left(i, x, p\right) = \operatorname{Function}.{update}\left(\operatorname{Function}.{update}\left(\operatorname{Function}.{update}\left(\operatorname{Function}.{update}\left(x, \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 0\right), \operatorname{Fin}.{mk}\left(\operatorname{Nat}.{mod}\left(\operatorname{Nat}.{div}\left(\operatorname{Fin}.{val}\left(p\right), (2)^{3}\right), 2\right)\right)\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 1\right), \operatorname{Fin}.{mk}\left(\operatorname{Nat}.{mod}\left(\operatorname{Nat}.{div}\left(\operatorname{Fin}.{val}\left(p\right), (2)^{2}\right), 2\right)\right)\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 2\right), \operatorname{Fin}.{mk}\left(\operatorname{Nat}.{mod}\left(\operatorname{Nat}.{div}\left(\operatorname{Fin}.{val}\left(p\right), (2)^{1}\right), 2\right)\right)\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 3\right), \operatorname{Fin}.{mk}\left(\operatorname{Nat}.{mod}\left(\operatorname{Nat}.{div}\left(\operatorname{Fin}.{val}\left(p\right), (2)^{0}\right), 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowUpdate` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

WindowUpdate replaces the four cyclic window coordinates by the four binary digits of p, in most-significant-first order, and leaves all other coordinates unchanged. Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.

**Definition 1.11 (The translated local channel).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (a: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n\right)\left(i\right)\left(a, x, y\right) = \sum_{p: \operatorname{Fin}\left(16\right)} \sum_{q: \operatorname{Fin}\left(16\right)} (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{localChannel}\left(\operatorname{Matrix}.{single}\left(p, q, (1: \mathbb{C})\right)\right)\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowCode}\left(i, x\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowCode}\left(i, y\right)\right)) \cdot (a\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowUpdate}\left(i, x, p\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowUpdate}\left(i, y, q\right)\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowChannel` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

WindowChannel inserts the four-site local channel into a cyclic n-site matrix by summing over the input and output window words and updating the two matrix indices accordingly.

**Definition 1.12 (The matrix of a window channel).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowSuperoperator}\left(n\right)\left(i\right) = \lambda (x: (((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \times ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))))) \mapsto (\lambda (y: (((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \times ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))))) \mapsto (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, i, \operatorname{Matrix}.{single}\left(\operatorname{Prod}.{fst}\left(y\right), \operatorname{Prod}.{snd}\left(y\right), (1: \mathbb{C})\right), \operatorname{Prod}.{fst}\left(x\right), \operatorname{Prod}.{snd}\left(x\right)\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowSuperoperator` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

WindowSuperoperator is the matrix-unit representation of a translated window channel on pairs of binary configurations.

**Definition 1.13 (The parent Lindbladian).**

$$\forall (n: \mathbb{N}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{parentLindbladian}\left(n\right) = \sum_{i \in \operatorname{Finset}.{filter}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Nat}.{mod}\left(\operatorname{Fin}.{val}\left(i\right), 2\right) = 0), \operatorname{Finset}.{univ}\left(\operatorname{Fin}\left(n\right)\right)\right)} ((\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowSuperoperator}\left(n, i\right)) - ((1: \operatorname{Matrix}\left((((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \times ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)))), (((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \times ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)))), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.parentLindbladian` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The parent Lindbladian is the sum of the translated channel minus the identity over zero-based even starting sites, corresponding to the source's odd-window sum after reindexing (main.tex l. 4951–4952). Nat.div denotes natural-number floor division and Nat.mod the remainder; Fin.divNat a b p and Fin.modNat a b p have values p.val / b and p.val % b, respectively.

**Definition 1.14 (The tensor product of bit flips).**

$$\forall (n: \mathbb{N}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{tensorX}\left(n\right) = \lambda (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\lambda (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{ite}\left(x = \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto ((y\left(j\right)) + (1)), (1: \mathbb{C}), (0: \mathbb{C})\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.tensorX` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

TensorX has one at the entry taking y to the configuration obtained by adding one in Fin 2 at every site, and zero elsewhere.

**Definition 1.15 (The ring controlled-Z operator).**

$$\forall (n: \mathbb{N}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{cz}\left(n\right) = \operatorname{Matrix}.{diagonal}\left(\lambda (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto ((-(1: \mathbb{C}))^{\sum_{j: \operatorname{Fin}\left(n\right)} (\operatorname{Fin}.{val}\left(x\left(j\right)\right)) \cdot (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(j, 1\right)\right)\right))})\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.cz` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Cz is diagonal, with phase minus one raised to the number of adjacent pairs of occupied bits around the cyclic ring.

**Definition 1.16 (The CZX unitary).**

$$\forall (n: \mathbb{N}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{czxUnitary}\left(n\right) = (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{cz}\left(n\right)) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{tensorX}\left(n\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.czxUnitary` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The CZX unitary is the controlled-Z operator followed by the tensor product of bit flips, in the source order.

**Definition 1.17 (Evolution under the parent generator).**

$$\forall (n: \mathbb{N}), \forall (t: \mathbb{R}), \forall (a: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{evolution}\left(n, t, a, x, y\right) = \operatorname{Matrix}.{mulVec}\left(\operatorname{NormedSpace}.{exp}\left(((t: \mathbb{C})) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{parentLindbladian}\left(n\right))\right), \lambda (p: (((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \times ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))))) \mapsto (a\left(\operatorname{Prod}.{fst}\left(p\right), \operatorname{Prod}.{snd}\left(p\right)\right))\right)\left((x, y)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.evolution` (`✓ std3`).

*Citation.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Evolution applies the matrix exponential of t times the parent Lindbladian to the vector of matrix entries and evaluates it at a pair of configurations.

**Definition 1.18 (The constant-sector gauge phase).**

$$\forall (n: \mathbb{N}), \forall (e: \operatorname{Fin}\left(2\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gauge}\left(n, e, x\right) = (-(1: \mathbb{C}))^{(\operatorname{Fin}.{val}\left(e\right)) \cdot (\sum_{j: \operatorname{Fin}\left(n\right)} (\operatorname{Fin}.{val}\left(x\left(j\right)\right)) \cdot (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(j, 1\right)\right)\right)))}$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.gauge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Gauge assigns to a bit e and configuration x the phase minus one raised to e times the cyclic nearest-neighbour occupation sum.

**Theorem 1.19 (Distinct sites in a four-site window).**

$$\forall (n: \mathbb{N}), (4 \le n) \Rightarrow (\forall (i: \operatorname{Fin}\left(n\right)), \forall (k: \operatorname{Fin}\left(4\right)), \forall (l: \operatorname{Fin}\left(4\right)), (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, \operatorname{Fin}.{val}\left(k\right)\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, \operatorname{Fin}.{val}\left(l\right)\right)) \Leftrightarrow (k = l))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.site_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

When n is at least four, the four cyclic positions from a fixed starting site are pairwise distinct. The proof cancels the common cyclic displacement modulo n.

**Definition 1.20 (The window channel as a linear map).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (a: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowLM}\left(n, i\right)\left(a\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, i, a\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowLM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

WindowLM is the complex-linear endomorphism whose action on every matrix is windowChannel.

**Definition 1.21 (A constant gauge window).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (\Delta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{goodWindow}\left(i, \Delta\right) = \forall (k: \operatorname{Fin}\left(4\right)), \Delta\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, \operatorname{Fin}.{val}\left(k\right)\right)\right) = \Delta\left(i\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.goodWindow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

GoodWindow holds when the gauge difference is constant on the four sites of the window.

**Definition 1.22 (The sector gauge phase).**

$$\forall (n: \mathbb{N}), \forall (\Delta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{sectorGauge}\left(n, \Delta, x\right) = (-(1: \mathbb{C}))^{\sum_{j: \operatorname{Fin}\left(n\right)} ((\operatorname{Fin}.{val}\left(\Delta\left(j\right)\right)) \cdot (\operatorname{Fin}.{val}\left(x\left(j\right)\right))) \cdot (\operatorname{Fin}.{val}\left(x\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(j, 1\right)\right)\right))}$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.sectorGauge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

SectorGauge is the product phase obtained by weighting every ring edge by the gauge difference at its source site.

**Definition 1.23 (A gauged matrix unit).**

$$\forall (n: \mathbb{N}), \forall (\Delta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gaugedUnit}\left(n, \Delta, x\right) = (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{sectorGauge}\left(n, \Delta, x\right)) \cdot (\operatorname{Matrix}.{single}\left((x) + (\Delta), x, (1: \mathbb{C})\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.gaugedUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

GaugedUnit is the sector phase times the matrix unit from x to x plus delta.

**Theorem 1.24 (Constant sectors recover the gauge).**

$$\forall (n: \mathbb{N}), \forall (e: \operatorname{Fin}\left(2\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{sectorGauge}\left(n, \operatorname{Function}.{const}\left(\operatorname{Fin}\left(n\right), e\right), x\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gauge}\left(n, e, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.sectorGauge_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

For a constant difference, distributing the constant over the finite sum identifies sectorGauge with gauge.

**Theorem 1.25 (The gauge phase is self-inverse).**

$$\forall (n: \mathbb{N}), \forall (\Delta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{sectorGauge}\left(n, \Delta, x\right)) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{sectorGauge}\left(n, \Delta, x\right)) = (1: \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.sectorGauge_mul_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Every sector gauge phase squares to one because its exponent is an integer and the sign square identity applies.

**Theorem 1.26 (The successor site map is injective).**

$$\forall (n: \mathbb{N}), \operatorname{Function}.{Injective}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 1\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.site_succ_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The cyclic successor map is injective for every nonempty Fin n. The proof uses the additive inverse in Fin n after establishing n is nonzero from an index.

**Theorem 1.27 (The gauged window action).**

$$\forall (n: \mathbb{N}), (4 \le n) \Rightarrow (\forall (i: \operatorname{Fin}\left(n\right)), \forall (\Delta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, i, \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gaugedUnit}\left(n, \Delta, x\right)\right) = \operatorname{ite}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{goodWindow}\left(i, \Delta\right), (((4: \mathbb{C}))^{-1}) \cdot (\sum_{b: \operatorname{Fin}\left(2\right)} \sum_{c: \operatorname{Fin}\left(2\right)} \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gaugedUnit}\left(n, \Delta, \operatorname{Function}.{update}\left(\operatorname{Function}.{update}\left(x, \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 1\right), b\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{site}\left(i, 2\right), c\right)\right)), (0: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.gauged_window_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

On a good window, the gauge converts the local channel into the uniform average over the two middle bits; on a bad window the action is zero. The phase change on the three affected edges cancels using the self-inverse gauge phase.

**Theorem 1.28 (Gauged units span the matrix space).**

$$\forall (n: \mathbb{N}), \forall (f: \operatorname{Module}.{End}\left(\mathbb{C}, \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)\right)), \forall (g: \operatorname{Module}.{End}\left(\mathbb{C}, \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)\right)), (\forall (\Delta: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), f\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gaugedUnit}\left(n, \Delta, x\right)\right) = g\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{gaugedUnit}\left(n, \Delta, x\right)\right)) \Rightarrow (f = g)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.matrix_linearMap_ext_gauged` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Two complex-linear endomorphisms agreeing on every gauged unit agree everywhere. Each standard matrix unit is a self-product of a sector phase times one gauged unit, so the standard matrix basis extension applies.

**Theorem 1.29 (Translated window channels commute).**

$$\forall (n: \mathbb{N}), (4 \le n) \Rightarrow (\forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), \forall (a: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, i, \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, j, a\right)\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, j, \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, i, a\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.window_channels_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The gauged-unit action identifies each good window channel with an average over its two middle coordinates. The coordinate averages commute, and the four cases of good or bad windows give equality for every matrix.

**Theorem 1.30 (The window superoperator action).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (a: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \forall (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{Matrix}.{mulVec}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowSuperoperator}\left(n, i\right), \lambda (p: (((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \times ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))))) \mapsto (a\left(\operatorname{Prod}.{fst}\left(p\right), \operatorname{Prod}.{snd}\left(p\right)\right))\right)\left((x, y)\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowChannel}\left(n, i, a, x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.window_superoperator_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

Applying LinearMap.toMatrix_mulVec_repr to windowLM in Matrix.stdBasis identifies the matrix-vector action of windowSuperoperator with windowChannel entrywise.

**Theorem 1.31 (Idempotence of a window superoperator).**

$$\forall (n: \mathbb{N}), (4 \le n) \Rightarrow (\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{IsIdempotentElem}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianWindowChannel}.{windowSuperoperator}\left(n, i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.window_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The local channel is idempotent on matrix units; the window channel therefore composes with itself to itself. The preceding action formula transfers this identity to the window superoperator.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.cz`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.czxU`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.czxUnitary`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.czxV`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.evolution`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.gauge`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.gaugedUnit`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.gauged_window_sector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.goodWindow`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.localChannel`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.matrix_linearMap_ext_gauged`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.mu`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.nu`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.parentLindbladian`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.renormS`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.renormT`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.sectorGauge`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.sectorGauge_const`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.sectorGauge_mul_self`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.site`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.site_injective`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.site_succ_injective`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.tensorX`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowChannel`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowCode`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowLM`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowSuperoperator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.windowUpdate`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.window_channels_commute`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.window_idempotent`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.window_superoperator_action`
- Dependency: [D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging](CZXParentLindbladianAveraging.md)
