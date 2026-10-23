---
bibkey: bourinlee2026symmetricmodulus
authors: J.-C. Bourin; E.-Y. Lee
year: 2026
title: "Triangle inequalities for the operator symmetric modulus"
doi: 10.1090/proc/17861
url: https://arxiv.org/abs/2602.19607v1
claim: "Corollary 4.2 gives the constant 1/4 for normal matrices in every dimension, proves sharpness for n ≥ 3, and the following paragraph asks for the best constant when n = 2."
strata_touched:
  - D5/S3/Quantum/Matrix/NormalModulusTriangleConstant
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2602.19607v1>.
J.-C. Bourin and E.-Y. Lee, *Triangle inequalities for the operator symmetric modulus*, arXiv:2602.19607v1, *Proceedings of the American Mathematical Society*, in press, doi:10.1090/proc/17861, §4, Corollary 4.2 and the following paragraph.

## Normal-matrix triangle inequality

Corollary 4.2 states verbatim:

> Corollary 4.2. Let A, B ∈ Mn be normal. Then, for some unitary V ∈ Mn, |A + B| ≤ |A| + |B| + (1/4) V(|A| + |B|)V*. If n ≥ 3, the constant 1/4 is the smallest possible one.

The following paragraph asks verbatim:

> However, contrarily to the Schur version (4.1), it seems necessary to request n ≥ 3 in Corollary 4.2 to get sharpness of 1/4 (what is the best constant for n = 2 ?).

The order is the positive-semidefinite order, and $|X|=(X^*X)^{1/2}$ denotes the positive modulus.

## Repository-derived result

The companion Lean theorem `result : ¬ claim` rules out every real constant $c<1/4$ in dimension two. The Hermitian witness is

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
M=\frac1{25}\begin{pmatrix}9&-12\\-12&16\end{pmatrix},\qquad B=-M.
$$

Here $|A|=A$, $|B|=M$, and $|A+B|=(4/5)I$. For $D=A+M$ and $x=(1,2)$, the quadratic forms are $x^*Dx=2$ and $x^*|A+B|x=4$. Positivity and $D\le(8/5)I$ imply $0\le x^*VDV^*x\le8$ for every unitary $V$. Thus $4\le2+c\,x^*VDV^*x$ is impossible when $c<1/4$, including negative $c$.

Together with the source's Corollary 4.2, this makes $1/4$ the attained best constant for $n=2$. The upper bound from that corollary is not formalized in the companion module.

## Neighboring references

Zhang, arXiv:2603.01046, and Aouichaoui–Lee, arXiv:2609.20094, are neighboring references. No theorem from either is used in the companion proof.

## ASSUMED-UNVERIFIED

The journal version's text is unverified; the quotations bind to arXiv:2602.19607v1, §4. The characterization “the positive square root is unique” is quoted, not proved or used by the Lean module. Its modulus predicate instead checks positivity and the square identity for each explicit matrix. No exhaustive literature or priority claim is established.
