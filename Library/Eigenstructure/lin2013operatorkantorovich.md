---
bibkey: lin2013operatorkantorovich
authors: Minghua Lin
year: 2013
title: "On an operator Kantorovich inequality for positive linear maps"
doi: 10.1016/j.jmaa.2013.01.015
url: https://arxiv.org/abs/1212.5690v1
claim: "Conjecture 3.4. Under the same condition as in Theorem 3.1. Then for every 2-positive linear map Φ, ‖Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX)Φ(X*AX)⁻¹‖ ≤ ((M−m)/(M+m))²."
strata_touched:
  - D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/1212.5690v1>.
- DOI: https://doi.org/10.1016/j.jmaa.2013.01.015

Minghua Lin, *On an operator Kantorovich inequality for positive linear maps*, J. Math. Anal. Appl. 402 (2013), 127–132; arXiv:1212.5690v1, §3, pp. 6–7.

## Operator Wielandt inequality and norm conjecture

§3, p. 6, Theorem 3.1 states verbatim:

> Theorem 3.1. [3] Let 0 < m ≤ A ≤ M and let X, Y be two partial isometries on H whose final spaces are orthogonal to each other. Then for every 2-positive linear map Φ, Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX) ≤ ((M−m)/(M+m))² Φ(X*AX).

§3, pp. 6–7, immediately before Conjecture 3.4:

> Despite the invalidity of (3.6), there is some evidence that the following assertion could be true. We have been unable to prove (or disprove) it.

§3, p. 7, Conjecture 3.4 states verbatim:

> Conjecture 3.4. Under the same condition as in Theorem 3.1. Then for every 2-positive linear map Φ, ‖Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX)Φ(X*AX)⁻¹‖ ≤ ((M−m)/(M+m))².

§3, p. 6, defines 2-positivity verbatim:

> Let Φ be a unital positive linear map between C*-algebras. We say that Φ is 2-positive if whenever the 2 × 2 operator matrix [[A, B],[B*, C]] is positive, then so is [[Φ(A), Φ(B)],[Φ(B*), Φ(C)]].

P. Zhang, *Remarks on an operator Wielandt inequality*, arXiv:1506.00737, describes Conjecture 3.4 as still open.

## Repository-derived result

Take $n=k=4$, $m=1/25$, $M=13$, and

$$
A=\begin{pmatrix}9&0&2&0\\0&2&1&0\\2&1&1&0\\0&0&0&1\end{pmatrix},\quad
X=P=\operatorname{diag}(1,1,0,0),\quad
Y=\begin{pmatrix}0&0&0&0\\0&0&0&0\\1&0&0&0\\0&1&0&0\end{pmatrix}.
$$

The complex-linear map $\Phi(Z)=PZP^*+YZY^*$ is unital and 2-positive. The two ranges are orthogonal and both $P,Y$ are partial isometries. Exact positive diagonal congruences certify $mI\le A\le MI$:

$$
A-mI=L\operatorname{diag}(224/25,49/25,33/9800,24/25)L^*,\quad
L=\begin{pmatrix}1&0&0&0\\0&1&0&0\\25/112&25/49&1&0\\0&0&0&1\end{pmatrix},
$$

$$
MI-A=U\operatorname{diag}(4,11,120/11,12)U^*,\quad
U=\begin{pmatrix}1&0&0&0\\0&1&0&0\\-1/2&-1/11&1&0\\0&0&0&1\end{pmatrix}.
$$

The compressed images are $\Phi(Y^*AY)=I$ and $D=\Phi(X^*AX)=\operatorname{diag}(9,2,9,2)$, with determinants 1 and 324. Their inverses are $I$ and $\operatorname{diag}(1/9,1/2,1/9,1/2)$.

The product in Conjecture 3.4 is

$$
T=\operatorname{diag}(G,G),\qquad
G=\begin{pmatrix}4/9&1\\2/9&1/2\end{pmatrix}.
$$

For the unit vector $e_2$ (index 1 in `Fin 4`),

$$
\|Te_2\|^2=5/4>\left(\frac{26244}{26569}\right)^2,
\qquad \left(\frac{M-m}{M+m}\right)^2=\frac{26244}{26569}<1.
$$

Thus the asserted Euclidean operator norm bound fails with both inverses genuine.

The Lean theorem `result : ¬ claim` proves the finite-dimensional refutation. Its norm predicate uses the Euclidean-space linear map of a complex matrix, not the entrywise matrix norm. The source's general assertion includes this instance.

## Neighboring references

P. Zhang, *Remarks on an operator Wielandt inequality*, <https://arxiv.org/abs/1506.00737>, studies consequences and symmetrized variants. The companion problem's Triage distinguishes the proved instance, exact reasoning, and the unresolved scope of those variants.

## ASSUMED-UNVERIFIED

The parameter-family analysis and consequences for conditional results are mathematical reasoning rather than additional Lean theorems.
