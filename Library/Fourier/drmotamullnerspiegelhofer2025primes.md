---
bibkey: drmotamullnerspiegelhofer2025primes
authors: Michael Drmota; Clemens Müllner; Lukas Spiegelhofer
year: 2025
title: Primes as sums of Fibonacci numbers
doi: 10.1090/memo/1537
url: https://arxiv.org/abs/2109.04068v2
claim: "Theorem 2.4 has a fixed-epsilon modulus range that eventually excludes the full support modulus of a superabundant candidate. Lemma 4.1 and classical prime equidistribution identify the actual five-window frequencies, conditional on the retained unit digit; they do not control a signed Robin margin."
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

## The actual five-window prime frequencies and the retained unit

**Lemma 4.1, author version v2, printed pp.36–37**, identifies a fixed
low-digit condition with an interval for the rotation of the **same**
integer. This detection lemma is already attributed there to DMS 2018,
Lemma 1, and Spiegelhofer's thesis, Proposition 5.7. Its prime-sampling
application uses classical Vinogradov equidistribution for an irrational
rotation. The recent [Chang–Verwee paper](changverwee2026terminalblocks.md),
Theorem 1.1 and the paragraph following it, explicitly makes this
attribution for the unit digit. The application below records the
parameter correspondence, not a new distribution theorem.

Use $F_2=1,F_3=2,F_4=3,F_5=5$ and the canonical nonadjacent digits
$a_j(n)$. Retain $h(n)=a_2(n)$ separately and define

$$
u(n)=\sum_{j=2}^5 a_j(n)F_j,\qquad
\chi(n)=\{F_j:3\le j\le5,\ a_j(n)=1\}.
$$

Thus $u\in\{0,\ldots,7\}$, and the five labels are exactly
$[null,2,3,2\ 5,5]$. They are occupancy patterns, not divisibility
conditions. Put $\varphi=(1+\sqrt5)/2$. Lemma 4.1 with its cutoff
parameter equal to 6 gives

$$
u(n)=u\iff n\varphi\in A_6(u)+\mathbb Z,
\qquad
A_6(u)=u\varphi+
\begin{cases}
(-\varphi^{-5},\varphi^{-6}),&0\le u<5,\\
(-\varphi^{-7},\varphi^{-6}),&5\le u<8.
\end{cases}
$$

The interval lengths are $\varphi^{-4}$ and $\varphi^{-5}$,
respectively. The source excludes endpoint hits for positive integers.
Vinogradov equidistribution therefore gives
$\#\{p\le X:u(p)=u\}/\pi(X)\to|A_6(u)|$ for these fixed eight
addresses. Grouping them by the actual unit digit and the user's
three-position window gives the following limiting frequencies. Each
conditional column uses the primes with its specified value of $h$ as
denominator.

| Window label | Low addresses $u$ | All primes | Given $h=0$ | Given $h=1$ |
|---|---|---|---|---|
| $null$ | $0,1$ | $2\varphi^{-4}$ | $\varphi^{-3}$ | $\varphi^{-2}$ |
| $2$ | $2$ | $\varphi^{-4}$ | $\varphi^{-3}$ | $0$ |
| $3$ | $3,4$ | $2\varphi^{-4}$ | $\varphi^{-3}$ | $\varphi^{-2}$ |
| $2\ 5$ | $7$ | $\varphi^{-5}$ | $\varphi^{-4}$ | $0$ |
| $5$ | $5,6$ | $2\varphi^{-5}$ | $\varphi^{-4}$ | $\varphi^{-3}$ |

The unit-zero addresses are $0,2,3,5,7$ and have total limiting mass
$3\varphi^{-4}+2\varphi^{-5}=\varphi^{-1}$. The unit-one addresses
are $1,4,6$ and have mass $2\varphi^{-4}+\varphi^{-5}=\varphi^{-2}$.
Dividing the joint masses by these positive unit masses gives the last
two columns. This retains the unit observation of the
[Beatty note](../ArithSums/guloglunevans2008beatty.md); its weighted
$Z(n)$ average is a different result and is not repeated here.

The conditional columns agree with the normalized subinterval lengths
of the existing golden-contraction sets
$K_0=[-1,\varphi]$ and $K_1=[-1,\varphi-1]$ in
[the FIB theory, §§150–151](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
Their lengths are $\varphi^2$ and $\varphi$, and their contraction
factor has absolute value $\varphi^{-3}$. In state 0, a branch with
successor 0 has relative length $\varphi^{-3}$, while a successor-1
branch has relative length $\varphi^{-4}$. In state 1, the two
successor-0 branches have relative length $\varphi^{-2}$ and the
successor-1 branch has relative length $\varphi^{-3}$.
These are length ratios and conditional sampling frequencies; this
comparison does not identify the two coordinate spaces or imply that
the unconditional five-window frequencies equal the state-0 ratios.

For every fixed finite legal prefix, the same detection and sampling
results are reusable. They do not provide a uniform error when the
prefix length grows with $X$, an estimate on a selected composite CA
chain, or a one-sided bound for its signed prime-error tail. Abel
summation also transfers a fixed-window frequency to its logarithmically
weighted prime sum, but supplies no error at the square-root scale
needed for Robin. The signed target remains the
[same-source residual](../Analytic/polak2026finiterobinca.md).
This application is a paper derivation with no new Lean declaration or
Lean verification.
