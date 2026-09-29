# The averaged enumerator of B-form codes

## Abstract

For every prime p, every c and every function t on Z/p with t(-a) = t(a), the full enumerator polynomial of the code with generating matrix (I | B^T), evaluated at x_ab = t_a t_b and averaged over the p^(c(c-1)/2) antisymmetric matrices B with zero diagonal, equals the cosine formula (barP) conjectured by N. Angelinos, D. Chakraborty and A. Dymarsky (arXiv:2206.14825).

**Definition 1.1 (B-form matrices).**

$$\operatorname{IsBForm}\left(B\right) \Leftrightarrow ((B^{T} = -B) \land (\forall i \in \operatorname{Fin}\left(c\right),\; B_{ii} = 0))$$

*Formalization.* `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.IsBForm` (`✓ std3`).

*Citation.* Nikolaos Angelinos; Debarghya Chakraborty; Anatoly Dymarsky (2022). *Optimal Narain CFTs from codes*. DOI: [10.48550/arXiv.2206.14825](https://doi.org/10.48550/arXiv.2206.14825). URL: <https://arxiv.org/abs/2206.14825v1>.

*Commentary.*

A c x c matrix B over Z/p is of B-form when it is antisymmetric and has zero diagonal; the code it generates has generating matrix (I | B^T).

**Definition 1.2 (The full enumerator at x_ab = t_a t_b).**

$$\operatorname{enumerator}\left(t, B\right) = \sum_{r \in (\mathbb{Z}/p)^{c}} \prod_{i} t\left(r_{i}\right) \cdot t\left((B^{T} r)_{i}\right)$$

*Formalization.* `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.enumerator` (`✓ std3`).

*Citation.* Nikolaos Angelinos; Debarghya Chakraborty; Anatoly Dymarsky (2022). *Optimal Narain CFTs from codes*. DOI: [10.48550/arXiv.2206.14825](https://doi.org/10.48550/arXiv.2206.14825). URL: <https://arxiv.org/abs/2206.14825v1>.

*Commentary.*

The codewords of the code of B are the pairs (r, B^T r) with r in (Z/p)^c. Its full enumerator is the sum over the codewords of the product over i of x_(r_i, (B^T r)_i); the paper evaluates it at x_ab = t_a t_b.

**Definition 1.3 (The conjectured average).**

$$claim \Leftrightarrow (\forall p \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow \left(\forall c \in \mathbb{N},\; \forall t \in \mathbb{Z}/p \to \mathbb{C},\; (\forall a \in \mathbb{Z}/p,\; t\left(-a\right) = t\left(a\right)) \Rightarrow \frac{\sum_{B \in \operatorname{Mat}\left(c, \mathbb{Z}/p\right), \operatorname{IsBForm}\left(B\right)} \operatorname{enumerator}\left(t, B\right)}{p^{\operatorname{natDiv}\left(c \cdot (c - 1), 2\right)}} = t\left(0\right)^{2 \cdot c} + \frac{\sum_{k \in \mathbb{Z}/p} (\sum_{a \in \mathbb{Z}/p} \sum_{b \in \mathbb{Z}/p} \operatorname{cos}\left(\frac{2\pi \cdot \operatorname{val}\left(k\right) \cdot \operatorname{val}\left(a\right) \cdot \operatorname{val}\left(b\right)}{p}\right) \cdot t\left(a\right) \cdot t\left(b\right))^{c} - p \cdot t\left(0\right)^{c} \cdot (\sum_{a \in \mathbb{Z}/p} t\left(a\right))^{c}}{p^{c}}\right))$$

*Formalization.* `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.claim` (`✓ std3`).

*Citation.* Nikolaos Angelinos; Debarghya Chakraborty; Anatoly Dymarsky (2022). *Optimal Narain CFTs from codes*. DOI: [10.48550/arXiv.2206.14825](https://doi.org/10.48550/arXiv.2206.14825). URL: <https://arxiv.org/abs/2206.14825v1>.

*Commentary.*

Eq. (barP) of the paper: the average of the enumerator over all B-form matrices, for every prime p, every c and every t with t(-a) = t(a). In the cosine, k, a and b are read as their representatives 0, ..., p - 1. In the exponent c(c - 1) is a natural number, natDiv is division of natural numbers rounded down and c - 1 is subtraction of natural numbers (0 at c = 0); c(c - 1) is even, so natDiv(c(c - 1), 2) = c(c - 1)/2 is the number of entries above the diagonal, and there are p^(c(c-1)/2) B-form matrices.

**Theorem 1.4 (Proof of the averaged formula).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.result` (`✓ std3`). ∎

*Resolves.* `Problems/angelinos-2022-bform-averaged-enumerator` (proved) by `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"angelinos-2022-bform-averaged-enumerator","declaration_gid":"D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nikolaos Angelinos; Debarghya Chakraborty; Anatoly Dymarsky (2022). *Optimal Narain CFTs from codes*. DOI: [10.48550/arXiv.2206.14825](https://doi.org/10.48550/arXiv.2206.14825). URL: <https://arxiv.org/abs/2206.14825v1>.

*Commentary.*

Exchange the sums over B and r. The term r = 0 gives t_0^(2c) for every B. For r nonzero, antisymmetry with zero diagonal gives r . B^T r = 0, and the linear map B -> B^T r is onto the hyperplane orthogonal to r: if r_j is nonzero, a matrix supported on row and column j reaches any s orthogonal to r. So each such s has the same number of preimages, and the sum over B equals p^(c(c-1)/2) / p^(c-1) times the sum over s orthogonal to r. The constraint r . s = 0 is written as p^(-1) times the sum over k of the standard additive character psi(k r . s); the sum over r and s then factors into the c-th power of the sum over a and b of psi(kab) t_a t_b, and the row r = 0 contributes p t_0^c (sum of t_a)^c. Since t is even, replacing (a, b) by (-a, b) turns psi(kab) into its complex conjugate, so the character sum equals the cosine sum. Counting the B-form matrices as p^(c(c-1)/2) gives the formula.

## References

- Truth anchor: `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.IsBForm`
- Truth anchor: `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.claim`
- Truth anchor: `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.enumerator`
- Truth anchor: `D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.result`
