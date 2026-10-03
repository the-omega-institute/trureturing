---
bibkey: debrota2017negativity
authors: John B. DeBrota; Christopher A. Fuchs
year: 2017
title: "Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations"
doi: 10.1007/s10701-017-0098-z
url: https://arxiv.org/abs/1703.08272v2
claim: "Section 6 conjectures that the Hoggar-SIC Q-minus representation in dimension 8 has global sum negativity 7/8; equations (8)–(12) define the negative part, sum negativity, maximum over density matrices, and SIC Q-reps."
strata_touched:
  - D5/S3/Quantum/Measurement/HoggarSicSumNegativity
license: citation-only
triage: anchor
---

# Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations

John B. DeBrota and Christopher A. Fuchs, arXiv:1703.08272v2 [quant-ph],
Foundations of Physics 47 (2017), 1009–1030. The following quotation is from
Section 6, page 17:

> Although dimension $5$ was the last in which we were able to explicitly calculate the sum negativity for the SIC Q-reps by exhaustive combinatorial searching, we suspect that we have found the correct sum negativity for $\{Q_j^-\}$ constructed with the Hoggar SIC in dimension $8$. Rather than calculating the eigenvalues of every partial sum matrix (since this is infeasible for $2^{64}$, $8\times8$ matrices), we used a numerical local maximization procedure and around $10^6$ random pure state seeds. The overall maximum value we found, $7/8$, occurred frequently in our data and is significantly larger than all of the smaller local maxima. Of course, we could still be falling short of the global maximum value if it occurs at very hard to access positions. The states whose quasiprobability representations achieve the sum negativity of $7/8$ consist of $28$ copies of value $-1/32$ and $36$ copies of value $5/96$.

The definition in equation (8), page 7, is
$\mathfrak p^{(-)}(j)=(|\mathfrak p(j)|-\mathfrak p(j))/2$:

> which replaces the positive elements of $\mathfrak{p}$ with zero and the negative elements with their absolute value.

Equation (9) defines $N^p(\mathfrak p)=\|\mathfrak p^{(-)}\|_p$, with $N^1$
called the *sum negativity*:

> We will refer to the special cases $N^1$ and $N^\infty$, which we see are equivalent to the two natural candidates proposed above, as the sum negativity and the ceiling negativity respectively.

Equations (10)–(11), pages 7–8, define
$N^p(\rho,\{Q_j\})=N^p(\mathfrak q)$ and
$N^p(\{Q_j\})=\max_\rho N^p(\rho,\{Q_j\})$.
There is no extra factor of $d$ in the paper's negativity convention.
Equation (12), page 8, is

$$Q_j^\pm=\mp\sqrt{d+1}\,\Pi_j+\frac{1\pm\sqrt{d+1}}d\,\mathbb I.$$

The minus choice at $d=8$ is $Q_j^-=3\Pi_j-\mathbb I/4$; the coordinates
are $\mathfrak q_\rho(j)=\operatorname{Tr}(\rho Q_j^-)/8$.
The formal statement takes the real part explicitly and quantifies over
all positive-semidefinite complex $8\times8$ matrices with trace one.
It states that $7/8$ is an attained greatest value, including mixed states.

## Hoggar realization

Blake C. Stacey, *Geometric and Information-Theoretic Properties of the Hoggar Lines*,
arXiv:1609.03075, equations (26)–(27), gives the fiducial
$(-1+2i,1,1,1,1,1,1,1)^T$ and its orbit under
$X^{k_0}Z^{k_1}\otimes X^{k_2}Z^{k_3}\otimes X^{k_4}Z^{k_5}$.
The encoding uses $j=8x+z$ and three binary bits for each of $x,z,b$.
The coefficient of $D_{x,z}v$ at $b$ is
$(-1)^{z\cdot(b+x)}v_{b+x}$, where binary addition is xor.
The squared vector norm is $12$, so $\Pi_j=u_ju_j^*/12$.

## Verified locator

- DOI: https://doi.org/10.1007/s10701-017-0098-z
- URL: https://arxiv.org/abs/1703.08272v2 — `sumneg.tex`, Section 6, page 17;
  definitions (8)–(12), pages 7–8. The arXiv PDF and TeX have both been read.
- Hoggar realization: https://arxiv.org/abs/1609.03075 — `qbic-hoggar.tex`,
  equations (26)–(27).
