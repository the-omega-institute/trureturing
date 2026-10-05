---
bibkey: lijiang2026highrank
authors: Bikun Li; Liang Jiang
year: 2026
title: "High-Rank Encoding Can Improve Approximate Quantum Error Correction"
doi: null
url: https://arxiv.org/abs/2609.00778v1
claim: "Exact optimality of this pair at fixed p > 0 remains open."
strata_touched:
  - D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation
license: citation-only
triage: anchor
---

# High-Rank Encoding Can Improve Approximate Quantum Error Correction

## Verified locator

- URL: https://arxiv.org/abs/2609.00778v1 (version 1, the source record inspected).
- Scope: printed p. 17 immediately after Eq. S64 for the fixed-noise optimality
  statement; Eqs. 18–23 and S60 on printed pp. 16–17 for the definitions used
  by the repository refutation.

Bikun Li and Liang Jiang, arXiv:2609.00778v1, 1 September 2026,
quant-ph. The source is this version, rather than an unverified later or
journal text. Printed p. 17, immediately after Eq. S64, states:

> Exact optimality of this pair at fixed p > 0 remains open.

The pair is $(\mathcal C_{V_p(\chi)},\operatorname{tr}_S)$, where Eq. S60
on printed p. 16 defines
$C_p(\chi)=Q_p(I_d\otimes|\chi\rangle)$ and
$V_p(\chi)=C_p(\chi)[C_p(\chi)^\dagger C_p(\chi)]^{-1/2}$.
The inverse square root is the positive Gram square root followed by its
inverse. The code space is $\mathbb C^d\otimes\mathbb C^d$ in logical,
auxiliary order; $\operatorname{tr}_S$ removes the right factor.

Eqs. 18–23 specify the actual noise. In the notation of the source module,

$$
\lambda_1=1-\frac p{d^2-2},\quad
\lambda_4=\frac{d^2-1+p}{d^2},\quad
\lambda_5=\frac{1-p}{d^2},\quad
\lambda_2=\frac{(1-\lambda_1)(d^2\lambda_1-1)}{d^2\lambda_4},\quad
\lambda_3=\frac{2(1-\lambda_1)^2}{d^2\lambda_4}.
$$

For $\psi=d^{-1/2}\sum_i|ii\rangle$ and $\Pi=|\psi\rangle\langle\psi|$,
Eq. 18 is
$Q_p=\sqrt d[\sqrt{\lambda_4/(d^2-1)}(I-\Pi)+\sqrt{\lambda_5}\Pi]$.
Eqs. 19 and 22 give $D_j=I\otimes\langle j|$,
$B_{ij}=QD_i^\dagger D_j$, and
$E_{ij}=(|ij\rangle\langle\psi|-\sqrt{\lambda_5}B_{ij}^\dagger)/\sqrt{\lambda_4}$.
Eq. 23 acts on every code matrix $X$ by

$$
\mathcal N_p(X)=\lambda_3\operatorname{tr}(X)I+
(\lambda_1-\lambda_3)\operatorname{tr}_S(Q_pXQ_p)\otimes I+
\lambda_2\sum_{i,j}E_{ij}XE_{ij}^\dagger.
$$

The optimization class in Eq. 13 comprises completely positive
trace-nonincreasing encoders and decoders, with encoder Choi rank at most
one for the rank-one optimum. The source uses input-first Choi order.
For $\tau=I_d/d$, its canonical-purification fidelity is the unrenormalized
overlap $\langle\psi|[(\mathcal D\circ\mathcal N_p\circ\mathcal C)
\otimes\mathrm{id}](|\psi\rangle\langle\psi|)|\psi\rangle$.
No output trace normalization is applied. The source admits $0\le p<1$;
the question at nonzero noise has $d\ge2$ and $0<p<1$.

The module refutes the universal exact-optimality reading at $d=2$,
$p=9/13$, $\chi=|0\rangle$. It preserves the actual noise and decoder and
replaces one polar column by a strictly better feasible column. It does
not determine the global rank-one optimum. The source's optimal
quadratic asymptotic coefficient in Eqs. S63–S64 and its high-rank
advantage theorem are not refuted.

The preregistration is [issue #13324](https://github.com/the-omega-institute/trureturing/issues/13324).
Its bounded literature check of 5 October 2026 reports
`not-found-in-searched-scope`. It inspected the single citing paper
arXiv:2609.40203v1, whose single-channel convex iteration does not settle
this joint pair question, and the unrelated author paper arXiv:2609.17439.
Semantic Scholar was rate limited; nonindexed/private work and worldwide
priority remain unverified. This note attributes the question and source
definitions to Li and Jiang; the refutation is a repository result.
