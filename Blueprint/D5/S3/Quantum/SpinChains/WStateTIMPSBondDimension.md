# A bond-dimension-3 translation-invariant MPS of the seven-qubit W-state

## Abstract

Two 3 x 3 matrices give a translation-invariant matrix product state representation with periodic boundary conditions of the normalized W-state of order 7. Its bond dimension 3 is smaller than floor(7/2) + 1 = 4. This refutes the conjecture of P. Klimov, R. Sengupta and J. Biamonte (arXiv:2306.16456) that no such representation of the W-state of order n has bond dimension smaller than floor(n/2) + 1, and shows that d(7) is at most 3, not 4 as in the paper's table.

**Definition 1.1 (Translation-invariant representations of the W-state).**

$$\forall n : \mathbb{N}, \forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsWStateTIMPS}\left(n, d, A\right) \Leftrightarrow (\forall w : \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{tr}\left(\prod_{i=0}^{n-1} A_{w_{i}}\right) = \operatorname{ite}\left(\sum_{i} w_{i} = 1, \frac{1}{\sqrt{n}}, 0\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.IsWStateTIMPS` (`✓ std3`).

*Citation.* Petr Klimov; Richik Sengupta; Jacob Biamonte (2023). *On Translation-Invariant Matrix Product States and advances in MPS representations of the W-state*. DOI: [10.48550/arXiv.2306.16456](https://doi.org/10.48550/arXiv.2306.16456). URL: <https://arxiv.org/abs/2306.16456v2>.

*Commentary.*

A pair A(0), A(1) of complex d x d matrices represents the normalized W-state of order n, as a translation-invariant matrix product state with periodic boundary conditions, when for every word w in {0, 1}^n the trace of the ordered product A(w_0) A(w_1) ... A(w_(n-1)) equals the amplitude of the basis vector |w> in the W-state: 1/sqrt(n) when w has exactly one letter 1, and 0 otherwise. In Lean the words are maps Fin n -> Fin 2 and the product is the product of a list in index order.

**Definition 1.2 (The conjecture).**

$$claim \Leftrightarrow (\forall n : \mathbb{N}, \forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \left((2 \le n) \land \operatorname{IsWStateTIMPS}\left(n, d, A\right)\right) \Rightarrow \left\lfloor\frac{n}{2}\right\rfloor + 1 \le d)$$

*Formalization.* `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.claim` (`✓ std3`).

*Citation.* Petr Klimov; Richik Sengupta; Jacob Biamonte (2023). *On Translation-Invariant Matrix Product States and advances in MPS representations of the W-state*. DOI: [10.48550/arXiv.2306.16456](https://doi.org/10.48550/arXiv.2306.16456). URL: <https://arxiv.org/abs/2306.16456v2>.

*Commentary.*

For every n >= 2, every d and all complex d x d matrices A(0), A(1) representing the W-state of order n, the bond dimension d is at least floor(n/2) + 1. The paper conjectures that no representation has bond dimension smaller than floor(n/2) + 1; the hypothesis n >= 2 only weakens the claim, and the paper's table of d(n) starts at n = 2. Here floor(n/2) is the natural-number division n / 2.

**Theorem 1.3 (Bond dimension 3 for n = 7).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result` (`✓ std3`). ∎

*Resolves.* `Problems/klimov-2023-w-state-ti-mps-bond-dimension` (refuted) by `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klimov-2023-w-state-ti-mps-bond-dimension","declaration_gid":"D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Petr Klimov; Richik Sengupta; Jacob Biamonte (2023). *On Translation-Invariant Matrix Product States and advances in MPS representations of the W-state*. DOI: [10.48550/arXiv.2306.16456](https://doi.org/10.48550/arXiv.2306.16456). URL: <https://arxiv.org/abs/2306.16456v2>.

*Commentary.*

Take A(0) = E_12 + E_21 + E_23 and A(1) = E_31 / sqrt(7), 3 x 3 matrices with E_ij the matrix units. Then A(0)^3 = A(0), and the (1, 3) entry of A(0)^r is 1 for even r >= 2 and 0 otherwise. The trace of a word with k >= 1 letters 1 is 7^(-k/2) times the product of the (1, 3) entries of A(0)^r over the k cyclic gaps r between consecutive letters 1, which add up to 7 - k. For k = 1 the gap is 6 and the trace is 1/sqrt(7). For k >= 2 the gaps cannot all be even and at least 2: that needs 3k <= 7, so k = 2, and then the two gaps add up to 5, which is odd. For k = 0 the trace of A(0)^7 = A(0) is 0. So the pair represents the W-state of order 7 with bond dimension 3 < 4. In Lean the 128 word traces of the integer matrices are computed by the kernel, and the factor 1/sqrt(7) is pulled out of each word.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.IsWStateTIMPS`
- Truth anchor: `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result`
