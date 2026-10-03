---
bibkey: bharadwajrodgers2026largeprimes
authors: Abhishek Bharadwaj; Brad Rodgers
year: 2026
title: "Large prime factors of well-distributed sequences"
doi: null
url: https://arxiv.org/abs/2402.11884v4
claim: "Prime-factor statistics for weighted integer populations with positive polynomial index, positive level of distribution, and congruence uniformity; the ordinary unweighted value set of a fixed Fibonacci recurrence fails the positive-index hypothesis."
strata_touched: []
license: citation-only
triage: anchor
---

# Large prime-factor statistics and the FIB sampling contract

The source is [arXiv:2402.11884v4](https://arxiv.org/pdf/2402.11884v4),
revised 9 April 2026; its first version appeared in February 2024.
The following locators refer to v4. They record the definitions and main
statements, not an independent audit of all proofs or a Lean verification.

## Population and hypotheses

For nonnegative weights $a_m$, Section 1.2, printed pp.2–3, defines

$$
N(x)=\sum_{m\le x}a_m,
\qquad
N_d(x)=\sum_{\substack{m\le x\\d\mid m}}a_m.
$$

Condition (A) requires $N(x)=x^{\alpha+o(1)}$ for some $\alpha>0$.
Condition (B) requires a level of distribution $\vartheta>0$: for each
$0<c<\vartheta$ and every $A>0$,

$$
\sum_{d\le x^c}|N_d(x)-g(d)N(x)|
\ll_{c,A}\frac{N(x)}{(\log x)^A}.
$$

The same condition requires a multiplicative $g(d)\in[0,1]$ satisfying
$\sum_{p\le x}g(p)\log p=\log x+O(1)$ and
$g(d)=O(C^{\Omega(d)}/d)$ for a constant $C\ge1$.
Condition (C), congruence uniformity, is

$$
N_d(x)\ll
\left(\frac{C^{\Omega(d)}}dN(x)+C^{\Omega(d)}\right)(\log x)^B
\qquad(d\le x)
$$

for fixed constants $B\ge0$ and $C\ge1$. The authors call the population
$\sigma$ well-distributed when (A), (B), and (C) hold and
$0<\sigma\le\min(\alpha,\vartheta)$.

## Exact statistical conclusions

Section 1.3 samples an integer $u$ with probability
$a_u/N(x)$ for $1\le u\le x$. Its prime factors $p_1\ge p_2\ge\cdots$
are listed with multiplicity.

- Theorem 7, printed p.5, gives convergence of the normalized prime-factor
  process to Poisson–Dirichlet when the population is 1 well-distributed.
- Lemma 8, printed p.6, gives correlation convergence for a $\sigma$
  well-distributed population only against compactly supported test functions
  in $\{(t_i):t_i>0,\ \sum_i t_i<\sigma\}$.
- Theorem 11, printed p.7, gives, for every $\varepsilon>0$,
  $\limsup_{x\to\infty}\mathbb P(P^+(u)\ge u^{1-\varepsilon})
  \ll\varepsilon$, with the constant depending on the population.

These are statements about the specified sampling law. Theorem 11 is an
upper bound on the frequency of exceptionally large largest prime factors,
not an upper bound on every selected integer's divisor response.

## Failed hypothesis for the ordinary fixed FIB value set

For a fixed nonzero nonnegative seed $(a,b)$, the
[FIB theory's Binet formula, §199](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
gives $V_j=aF_{j+3}+bF_{j+4}=c_v\phi^j+O_v(|\psi|^j)$, where $c_v>0$.
Under the ordinary indicator $a_m=\mathbf1_{\{m=V_j\text{ for some }j\ge0\}}$,
the values are eventually strictly increasing, and therefore

$$
N(x)=\frac{\log x}{\log\phi}+O_v(1),
\qquad
\frac{\log N(x)}{\log x}\longrightarrow0.
$$

Condition (A) fails: this population has no positive polynomial index.
Consequently the paper's main results cannot be applied directly to that
unweighted recurrence family, even before testing conditions (B) and (C).
Taking a uniform random index $j\le J$ does not change the fact that
the paper's cutoff $x$ is the size of the integer value, not its index.

Reweighting the values or allowing seeds to vary changes the population;
all three conditions and transport back to the desired actual candidates
would then need separate proofs. No impossibility of every such alternative
weighting is asserted here. Using all canonical FIB encodings instead
recovers the ordinary integer population; its statistical theorem still
does not control a specified extremal Robin candidate.

The remaining joint weight in FIB §233.5 is attached to one actual integer
and its own divisors. Neither a distributional limit nor a density-one
conclusion replaces that estimate, and this note introduces no new
prime-factor statistical theorem.
