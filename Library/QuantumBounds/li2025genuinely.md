---
bibkey: li2025genuinely
authors: D. Li
year: 2025
title: "A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero coefficients"
doi: 10.48550/arXiv.2510.16561
url: https://arxiv.org/abs/2510.16561v1
claim: "Section 6 asks how many forms of the corresponding 2 by p coefficient matrix exist for a separable, not trivially separable n-qubit state with m = 2p non-zero coefficients (p prime), after recording two forms for m = 4 and four forms for m = 6."
strata_touched:
  - D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms
license: citation-only
triage: anchor
---

# Li, genuinely entangled n-qubit states with six non-zero coefficients

D. Li, *A necessary and sufficient condition for genuinely entangled n-qubit states with six
non-zero coefficients*, arXiv:2510.16561v1 (18 October 2025; quant-ph).

## Verified locator

DOI: 10.48550/arXiv.2510.16561.
Primary version: https://arxiv.org/abs/2510.16561v1 (the only arXiv version).
The TeX source `iff-m=6--e-print.tex` of v1 supplies the ordered basis states (Section 2,
Eq. (1), label `order`), trivial separability (Section 2), the four $m=6$ forms (Section 2,
labels `mt-1`, `mt-2`, `mt-3`, `mt-5`), the separable form for $m=2p$ (Section 6, label `dis-1`,
printed as Eq. (120)) and the closing question (Section 6, lines 924–927).

## Source statements

Ordered basis states (Section 2): "let $|\psi\rangle_{1\cdots n}=\sum_{i=1}^{6}b_i|B_i\rangle_{1\cdots n}$,
where $b_i\neq0$, $i=1,..,6$ and $|B_i\rangle_{1\cdots n}$ are basis states, where $B_i$ are binary
numbers $\varepsilon_1^{(i)}\varepsilon_2^{(i)}\ldots\varepsilon_n^{(i)}$ […] and
$B_1<B_2<B_3<B_4<B_5<B_6$."

Trivial separability (Section 2): "When $|\psi\rangle_{1\cdots n}=|0\rangle_i|\varphi\rangle_{12\cdots n/i}$
($|1\rangle_i|\phi\rangle_{12\cdots n/i}$), it means the ith qubit is 0 (1) in each basis state
[…]. We call it a trivially separable state."

The $m=6$ forms (Section 2): "Via the six coefficients $b_1,\cdots,b_6$, we can make $6!(=720)$
$2$ by $3$ matrices with the entries $b_i$. We will show that the corresponding coefficient
matrices $\Delta$ are of the following four forms": $\begin{pmatrix}b_1&b_2&b_5\\b_3&b_4&b_6\end{pmatrix}$,
$\begin{pmatrix}b_1&b_3&b_5\\b_2&b_4&b_6\end{pmatrix}$, $\begin{pmatrix}b_1&b_2&b_3\\b_4&b_5&b_6\end{pmatrix}$,
$\begin{pmatrix}b_1&b_3&b_4\\b_2&b_5&b_6\end{pmatrix}$.

The case $m=2p$ (Section 6): "Let $|\psi\rangle_{1\cdots n}$ be a pure state of $n$ qubits and $m$ be
the number of non-zero coefficients of $|\psi\rangle_{1\cdots n}$, where $m=2p$, where $p$ is a
prime. […] Assume that $|\psi\rangle_{1\cdots n}$ is not trivially separable. Then if
$|\psi\rangle_{1\cdots n}$ is separable, then it can be written as
$(\alpha_1|0_1\gamma_2\cdots\gamma_k\rangle+\alpha_2|1_1\gamma_2'\cdots\gamma_k'\rangle)_{p_1\cdots p_k}\otimes
(\beta_1|\sigma_1^{(1)}\cdots\sigma_s^{(1)}\rangle+\cdots+\beta_p|\sigma_1^{(p)}\cdots\sigma_s^{(p)}\rangle)_{q_1\cdots q_s}$",
with "the following corresponding coefficient matrix
$\begin{pmatrix}\alpha_1\beta_1&\cdots&\alpha_1\beta_p\\\alpha_2\beta_1&\cdots&\alpha_2\beta_p\end{pmatrix}$."

Question (Section 6): "What to do next is how to find the forms of the corresponding coefficient
matrices. When $m=4$, there are two forms [Li-24]. When $m=6$, there are four forms. How many forms
of the corresponding coefficient matrices are there when $m=2p$?"

## Scope

The paper proves a necessary and sufficient condition for genuine entanglement of $n$-qubit states
with six non-zero coefficients and lists the four $m=6$ forms. The count for general $m=2p$ is left
as the closing question.
