---
bibkey: drmotamullnerspiegelhofer2025primes
authors: Michael Drmota; Clemens Müllner; Lukas Spiegelhofer
year: 2025
title: Primes as sums of Fibonacci numbers
doi: 10.1090/memo/1537
url: https://arxiv.org/abs/2109.04068v2
claim: "Theorem 2.4 gives level-one distribution for the Zeckendorf digit-sum phase, with a fixed-epsilon modulus range. The full initial-prime support modulus of an actual superabundant candidate eventually lies outside every such fixed range at its own size."
strata_touched: []
license: citation-only
triage: anchor
---

# Zeckendorf digital distribution and the full support modulus

Published as Memoirs of the American Mathematical Society **305**, memoir 1537
(2025), [DOI:10.1090/memo/1537](https://doi.org/10.1090/memo/1537).
The theorem inspected here is from the authors'
[arXiv:2109.04068v2](https://arxiv.org/pdf/2109.04068v2), updated
2022-08-16, **§2.5.1, Theorem 2.4, equation (2.5), printed p.12**.
The publisher PDF was not available at the inspected endpoint; theorem
numbering is therefore assigned to that specified author version.
The statement and the parameter comparison below were checked, not the
complete analytic proof. The application has no Lean verification and
is not claimed as new mathematics or a Robin proof.

## What level one means in the quoted theorem

Let $s_\varphi(n)$ be the number of occupied positions in the canonical
Zeckendorf representation, $e(t)=\exp(2\pi it)$ and
$\|\theta\|=\min_{k\in\mathbb Z}|\theta-k|$. For each fixed
$\varepsilon>0$, there exist $c_\varepsilon,C_\varepsilon>0$,
depending only on $\varepsilon$, such that for every real $X\ge1$ and
$\theta\in\mathbb R$,

$$
\sum_{1\le d\le X^{1-\varepsilon}}
\max_{\substack{0\le u\le v\\v-u\le X}}
\max_{0\le b<d}
\left|\sum_{\substack{u\le n<v\\n\equiv b\pmod d}}
e\!\left(\theta s_\varphi(n)\right)\right|
\le C_\varepsilon(\log^+X)^{11/4}
X^{1-c_\varepsilon\|\theta\|^2}.
\tag{1}
$$

Here $\log^+X=\max(1,\log X)$. The interval location is uniform,
and a fixed admissible modulus can be extracted from the nonnegative
outer sum. The theorem still has a fixed positive $\varepsilon$:
“level one” does not assert a uniform bound through $d=X$, or permit
$\varepsilon$ to tend to zero without control of its constants.
At integral $\theta$, the displayed bound has no power saving; that
degenerate phase is included in the statement.

## The actual extremal support has a different scale

Reuse [Alaoglu–Erdős](../Arith/alaoglu1944highly.md),
*On highly composite and similar numbers*, §2, **Theorems 1 and 7**.
The inspected [original text](https://www.renyi.hu/~p_erdos/1944-03.pdf)
places Theorem 7 on printed p.454. For superabundant $n$, including
colossally abundant integers, these classical inputs give initial-prime
support and

$$
P=P^+(n)\sim\log n,\qquad
R=P\#=\prod_{p\le P}p\mid n.
$$

The prime number theorem then gives

$$
\log R=\vartheta(P)\sim\log n,\qquad
R=n^{1-o(1)}.
\tag{2}
$$

Thus at $X\asymp n$, the single modulus imposing all divisibilities
$p\mid n$ for $p\le P$ eventually satisfies
$R>X^{1-\varepsilon}$ for every fixed $\varepsilon>0$.
The range in (1) consequently cannot encode that complete support at
the candidate's own scale. The higher prime-power valuations are
additional restrictions, beyond this already too-large support modulus.

This diagnoses the **full-support substitution**, rather than all
possible uses of (1). Smaller subsets of support primes may fall within
its range. Taking a larger $X$ can also make $R$ admissible, but (1)
then carries the larger absolute error and supplies no estimate below
one that isolates the original integer. Uniformity in interval location
does not eliminate the dependence on interval-length bound $X$.

## The observable must also be transported

The phase in (1) counts all Zeckendorf digits. It is not the complete
golden norm, discriminant square class, canonical displacement, or
exponent-sensitive Euler deficit of that same $n$. A transfer requires
an estimate for the required observable and its weights, not just the
availability of a canonical digit encoding. The
[weighted Beatty note](../ArithSums/guloglunevans2008beatty.md) retains
the actual unit bit and $Z(n)$, but likewise supplies only an average.

The earlier result *Möbius orthogonality for the Zeckendorf sum-of-digits
function*, Theorem 1, is already cited in
[the FIB theory, §148.2](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md);
it is not supplied again as a new input here. The effective pointwise
fixed-digit and fixed-support results of Bugeaud are likewise already
recorded in the [complementary-divisor note](../ArithSums/fibcomplement2026weightedresidues.md).
Neither the moving full-support modulus nor the same-candidate weighted
estimate follows from these cited results.
