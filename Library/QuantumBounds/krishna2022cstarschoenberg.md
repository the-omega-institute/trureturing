---
bibkey: krishna2022cstarschoenberg
authors: K. Mahesh Krishna
year: 2022
title: "C*-algebraic Schoenberg Conjecture"
doi: 10.48550/arXiv.2206.06653
url: https://arxiv.org/abs/2206.06653v1
claim: "Section 2 defines the ordered derivative P′ and states Conjectures 2.1, 2.3 and 2.4; Theorem 2.2 proves the degree-two case of Conjecture 2.1."
strata_touched:
  - D5/S3/Quantum/Algebra/CStarSchoenberg
  - D5/S3/Quantum/Algebra/CStarDeBruinSharma
  - D5/S3/Quantum/Algebra/CStarKushelTyaglov
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2206.06653

Source: https://arxiv.org/abs/2206.06653v1

# C*-algebraic Schoenberg Conjecture

K. Mahesh Krishna, "C*-algebraic Schoenberg Conjecture", arXiv:2206.06653v1 (14 June 2022; single version), Section 2.

> Let $\mathcal{A}$ be a C*-algebra. Given $P(z) \coloneqq (z-a_1)(z-a_2)\cdots (z-a_d)$ for all $z\in \mathcal{A}$ with $a_1, a_2, \dots, a_d \in \mathcal{A}$, we define $P'(z)=\sum_{j=1}^{d}(z-a_1)\cdots \widehat{(z-a_j)}\cdots (z-a_d), \quad \forall z \in \mathcal{A}$ where the term with cap is missing.

> **Conjecture 2.1 (C*-algebraic Schoenberg Conjecture).** Let $\mathcal{A}$ be a C*-algebra. Let $d\in \mathbb{N}\setminus\{1\}$, $P(z) \coloneqq (z-a_1)(z-a_2)\cdots (z-a_d)$ be a polynomial over $\mathcal{A}$ with $a_1, a_2, \dots, a_d \in \mathcal{A}$. If $P'$ can be written as $P'(z)= d(z-b_1)(z-b_2)\cdots (z-b_{d-1})$ on $\mathcal{A}$ with $b_1, b_2, \dots, b_{d-1} \in \mathcal{A}$, then
> $$\sum_{k=1}^{d-1}b_kb_k^*\leq \frac{1}{d^2}\left[\sum_{j=1}^{d}a_j\right]\left[\sum_{j=1}^{d}a_j\right]^*+ \frac{d-2}{d}\sum_{j=1}^{d}a_ja_j^*$$
> and
> $$\sum_{k=1}^{d-1}b_k^*b_k\leq \frac{1}{d^2}\left[\sum_{j=1}^{d}a_j\right]^*\left[\sum_{j=1}^{d}a_j\right]+ \frac{d-2}{d}\sum_{j=1}^{d}a_j^*a_j.$$

> **Conjecture 2.3 (C*-algebraic de Bruin-Sharma Conjecture).** Let $\mathcal{A}$ be a C*-algebra, $d\in \mathbb{N}\setminus\{1\}$ and let $P(z) \coloneqq (z-a_1)(z-a_2)\cdots (z-a_d)$ be a polynomial over $\mathcal{A}$ with $a_1, a_2, \dots, a_d \in \mathcal{A}$. Assume that $P'$ can be written as $P'(z)\coloneqq d (z-b_1)\cdots (z-b_{d-1})$ on $\mathcal{A}$ with $b_1, b_2, \dots, b_{d-1} \in \mathcal{A}$. If $\sum_{j=1}^{d}a_j=0,$ then
> $$\sum_{k=1}^{d-1}(b_kb_k^*)^2\leq \frac{2}{d^2}\left(\sum_{j=1}^{d}a_ja_j^*\right)^2+ \frac{d-4}{d}\sum_{j=1}^{d}(a_ja_j^*)^2$$
> and
> $$\sum_{k=1}^{d-1}(b_k^*b_k)^2\leq \frac{2}{d^2}\left(\sum_{j=1}^{d}a_j^*a_j\right)^2+ \frac{d-4}{d}\sum_{j=1}^{d}(a_j^*a_j)^2.$$

> **Conjecture 2.4 (C*-algebraic Kushel-Tyaglov Conjecture).** Let $\mathcal{A}$ be a C*-algebra, $n\in \mathbb{N}\setminus\{1\}$ and let $P(z) \coloneqq (z-a_1)(z-a_2)\cdots (z-a_d)$ be a polynomial over $\mathcal{A}$ with $a_1, a_2, \dots, a_d\in \mathcal{A}$. Assume that $P'$ can be written as $P'(z)\coloneqq d (z-b_1)\cdots (z-b_{d-1})$ on $\mathcal{A}$ with $b_1, b_2, \dots, b_{d-1} \in \mathcal{A}$. Then
> $$\sum_{k=1}^{d-1}(b_kb_k^*)^2\leq \frac{d-6}{d}\sum_{j=1}^{n}(a_ja_j^*)^2+\frac{1}{d^2}\left(\sum_{j=1}^{d}a_ja_j^*\right)^2+ \frac{1}{d^2}\left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right] \left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right]^* +\frac{2}{d}\sum_{j=1}^{d}a_j\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]^*a_j^*-\frac{4}{d^3}\sum_{j=1}^{d}a_j \left[\sum_{k=1}^{d}a_k \right] \left[\sum_{k=1}^{d}a_k \right]^*a_j^*$$
> and
> $$\sum_{k=1}^{d-1}(b_k^*b_k)^2\leq \frac{d-6}{d}\sum_{j=1}^{d}(a_j^*a_j)^2+\frac{1}{d^2}\left(\sum_{j=1}^{d}a_j^*a_j\right)^2+ \frac{1}{d^2}\left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right]^* \left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right] +\frac{2}{d}\sum_{j=1}^{n}a_j^*\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]^*\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]a_j-\frac{4}{d^3}\sum_{j=1}^{d}a_j^* \left[\sum_{k=1}^{d}a_k \right]^* \left[\sum_{k=1}^{d}a_k \right]a_j.$$

> **Theorem 2.2.** Conjecture 2.1 holds for C*-algebraic polynomials of degree 2.

The source proves Conjecture 2.1 for d = 2 (Theorem 2.2) and states that Conjecture 2.3 holds for d = 2. In Conjecture 2.4 the index $n$ is bound, and $d$ is otherwise free while the sums run to $n$ in two places. The encoding reads n as d.


The definition of P′ and Conjecture 2.1 begin on page 2; Conjecture 2.1 continues
on page 3. Theorem 2.2 and Conjecture 2.3 occur on page 3. Conjecture 2.4 spans
pages 3–4. In Conjecture 2.4, the encoding reads the printed n as d. Indices become zero-based Fin types, while the product order is retained.

The source quantifies over C*-algebras. The encoding quantifies over unital
C*-algebras in Type, with PartialOrder and StarOrderedRing, and d ≥ 2. These are
restrictions of the universal assertion, so a counterexample in this subclass
refutes the source assertion. The counterexample has degree three, leaving the
source's degree-two result intact.
