---
bibkey: hayajneh2018uinorm
authors: Mostafa Hayajneh; Saja Hayajneh; Fuad Kittaneh
year: 2018
title: On some classical trace inequalities and a new Hilbert–Schmidt norm inequality
doi: 10.7153/mia-2018-21-81
url: https://doi.org/10.7153/mia-2018-21-81
claim: Conjecture 1 proposes monotonicity of the mixed-power expression in every unitarily invariant norm for positive semidefinite A and Hermitian B.
strata_touched:
  - D5/S3/Quantum/Schatten/TraceNorm
  - D5/S3/Quantum/Matrix/HayajnehConjectureRefutation
license: citation-only
triage: anchor
---

# On some classical trace inequalities and a new Hilbert–Schmidt norm inequality

## Locator

- Journal: *Mathematical Inequalities & Applications* 21(4) (2018), 1175–1183.
- DOI: https://doi.org/10.7153/mia-2018-21-81.
- Journal PDF: https://files.ele-math.com/articles/mia-21-81.pdf.
- Location: §1, Conjecture 1, printed p. 1177.
- The pinned source is the journal version. No arXiv identifier is asserted.

## Source statement and definitions

> CONJECTURE 1. Let A be a positive semidefinite matrix and B be a Hermitian matrix. Then for 1/2 ⩽ s ⩽ t ⩽ 1 and for every unitarily invariant norm, we have |||A^s B + BA^{1−s}||| ⩽ |||A^t B + BA^{1−t}|||.

The statement quantifies over every finite dimension, all complex positive semidefinite matrices $A$, all complex Hermitian matrices $B$, all real parameters $1/2\le s\le t\le1$, and every unitarily invariant norm on that matrix space. Real powers use continuous functional calculus. The conjecture imposes no requirement $A\ge I$ and no spectral-range restriction.

## Counterexample

Take

$$
A=\begin{pmatrix}1/81&0\\0&1\end{pmatrix},\qquad
B=\begin{pmatrix}1&3/4\\3/4&1\end{pmatrix},\qquad
s=\frac12,\quad t=\frac34.
$$

Both matrices are positive definite: their eigenvalues are $1/81,1$ and $1/4,7/4$, respectively. In particular, the required positive semidefiniteness and Hermitian hypotheses hold. Functional calculus on the diagonal matrix gives

$$
A^{1/2}=\operatorname{diag}(1/9,1),\quad
A^{1/4}=\operatorname{diag}(1/3,1),\quad
A^{3/4}=\operatorname{diag}(1/27,1).
$$

Consequently the two compared matrices are

$$
L=A^{1/2}B+BA^{1/2}=\begin{pmatrix}2/9&5/6\\5/6&2\end{pmatrix},\qquad
R=A^{3/4}B+BA^{1/4}=\begin{pmatrix}10/27&7/9\\1&2\end{pmatrix}.
$$

For every complex two by two matrix $T$, the trace norm satisfies

$$
\|T\|_1^2=\operatorname{tr}(T^*T)+2|\det T|.
$$

Indeed, if its singular values are $\sigma_1,\sigma_2\ge0$, then $\sigma_1^2+\sigma_2^2=\operatorname{tr}(T^*T)$ and $\sigma_1\sigma_2=|\det T|$. This identity applies to $R$ even though $R$ is not Hermitian. Here

$$
\det L=-\frac14,\quad \det R=-\frac1{27},\qquad
\|L\|_1^2=\frac{481}{81},\quad \|R\|_1^2=\frac{4240}{729}.
$$

Thus

$$
\|L\|_1^2-\|R\|_1^2=\frac{89}{729}>0,
\qquad \|L\|_1>\|R\|_1.
$$

The trace norm is unitarily invariant, so this strict reverse comparison refutes Conjecture 1. It also violates the proposed singular-value weak majorization at its full prefix $k=2$, the sum of both singular values.

## Scope and literature boundary

The conjecture and the known positive cases are attributed to Hayajneh, Hayajneh and Kittaneh. The explicit rational matrices and exact trace-norm comparison are repository derivations. The source proves the Hilbert–Schmidt case in §2 and the endpoint case $s=1/2,t=1$ for all unitarily invariant norms on p. 1179: “This affirmatively settles Conjecture 1 for the case s = 1/2 and t = 1.” Neither case is contradicted by the example.

The literature check covered the DOI and title with conjecture/counterexample/proof; "Hayajneh" "Conjecture 1"; and A^s B + BA^{1−s} with unitarily invariant norm. Related work checked: S. Hayajneh, *Filomat* 38(19) (2024), 6891–6896, which reproves a related scalar trace inequality; Bottazzi–Elencwajg–Larotonda–Varela, arXiv:1403.7472, which concerns a different expression, A^tB^{1−t} + B^tA^{1−t}. No settlement of Conjecture 1 was found within that scope. Citation indexes were not exhaustively checked.

For the displayed pair, numerical evaluation gives the conjectured direction for Schatten $p\in\{1.5,2,3,\infty\}$. This finite list does not establish the inequality for all Schatten $p\ge2$ or for the operator norm on arbitrary inputs. Those restricted universal questions remain open here. Absence of later settlements and worldwide priority are not established. This citation-only note incorporates no external source software.
