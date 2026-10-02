---
bibkey: bilugunhong2022uniform
authors: Yuri Bilu; Sanoli Gun; Haojie Hong
year: 2022
title: "Uniform explicit Stewart's theorem on prime factors of linear recurrences"
doi: null
url: https://arxiv.org/abs/2108.09857v5
claim: "Theorem 1.3 gives a field-uniform explicit lower bound for a rational prime below a prime ideal dividing gamma^n-1, for quadratic gamma of norm plus or minus one; it does not bound the total reciprocal prime-factor mass of a general Fibonacci combination."
strata_touched: []
license: citation-only
triage: anchor
---

# Uniform explicit Stewart input and the actual recurrence

The statements are pinned to [arXiv:2108.09857v5](https://arxiv.org/pdf/2108.09857v5).
The first preprint appeared in 2021; the cited arXiv version is dated 2 October
2022. The title page orders the authors Bilu, Gun, Hong. This note checks the
theorem statements and the cyclotomic interface in their proof, without
claiming an independent verification of the analytic proof or Lean evidence.

## Credited theorem and quantitative scope

Theorem 1.3, printed p.2, assumes that $\gamma$ is nonzero, has degree two,
is not a root of unity, and has field norm $\pm1$. With
$K=\mathbb Q(\gamma)$ and absolute field discriminant $D_K$, set

$$
n_0=\exp\exp\bigl(\max\{10^9,3|D_K|\}\bigr).
$$

For every $n\ge n_0$, there is a prime ideal $\mathfrak p$ of $K$, above a
rational prime $p$, such that

$$
v_{\mathfrak p}(\gamma^n-1)\ge1,
\qquad
p\ge n\exp\!\left(0.0002\frac{\log n}{\log\log n}\right).
$$

The threshold is independent of $h(\gamma)$ and its finite prime support,
but depends on the field. This strengthens the explicitness and uniformity
of Stewart's result; it is not a new largest-prime theorem of this project.
Stewart's earlier cyclotomic lower bound is already used in
[PERIODIC_TREE, FD.2](../../docs/develop/theory/PERIODIC_TREE.md).

Theorems 1.4 and 1.5, printed pp.2–3, give upper bounds on individual
$\mathfrak p$-adic valuations of $\gamma^n-1$. The latter's bound retains
$h(\gamma)\log^*n$ and an explicit prime threshold. It is neither a bound
for all primes dividing a different recurrence nor an upper bound on their
unweighted reciprocal sum.

## Parameter mapping for Fibonacci and Lucas blocks

Use $\phi=(1+\sqrt5)/2$, $\psi=(1-\sqrt5)/2$, and
$\tau=\phi/\psi=-\phi^2$. Then $K=\mathbb Q(\sqrt5)$, $D_K=5$,
$\operatorname N(\tau)=1$, and $\tau$ is not a root of unity. The identity

$$
\tau^n-1=\frac{\sqrt5\,F_n}{\psi^n}
$$

transports the theorem's large rational prime to a divisor of $F_n$:
$\psi$ is a unit and the displayed lower bound excludes $p=5$.
This is a direct application of the published result.

For Lucas numbers, merely applying the stated theorem to $\tau^{2n}-1$
and using $F_{2n}=F_nL_n$ would not identify which factor contains the
prime. The stronger locator is Section 10, printed pp.19–21: its proof
bounds the largest underlying rational prime dividing $\Phi_m(\tau)$.
At $m=2n$, $\Phi_{2n}(X)$ divides $X^n+1$; the large prime therefore
divides $L_n$, using $\tau^n+1=L_n/\psi^n$. This application requires
$2n\ge n_0$. The cyclotomic locator, rather than the product alone,
supplies the factor selection.

## What cannot be transported to a general seed

The actual fixed-seed family in the
[FIB theory, §§191 and 199](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
is $V_j=aF_{j+3}+bF_{j+4}$, with $v=a+b\phi$ and
$\rho=v'/v$. Its Binet numerator and good-prime condition are

$$
\sqrt5\,V_j=\phi^{j+3}v-\psi^{j+3}v',
\qquad
p\mid V_j\ \Longleftrightarrow\ \tau^{j+3}\equiv\rho\pmod{pR}
\quad(p\nmid5\operatorname N(v)).
$$

The nonconstant target $\rho$ cannot be dropped when applying a theorem
about $\gamma^n-1$. A general seed has not thereby become a Lucas sequence.
The unit and norm-five reductions to Fibonacci and Lucas blocks are
already present in §199.5 and are reused.

Even for a block with a certified large prime, the theorem gives an
existential lower bound for one prime. It does not give an upper bound on
$\sum_{p>y,\,p\mid V_j}1/(p-1)$ or the full divisor weight of the same
actual integer. Sections 199–201 already contain stronger fixed-seed and
restricted changing-seed Robin conclusions; the remaining general
changing-seed and same-candidate budgets are not settled by this source.
