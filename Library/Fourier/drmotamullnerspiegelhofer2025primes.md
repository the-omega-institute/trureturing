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
results are reusable. These sampling statements alone do not provide a uniform error when the
prefix length grows with $X$, an estimate on a selected composite CA
chain, or a one-sided bound for its signed prime-error tail. Abel
summation also transfers a fixed-window frequency to its logarithmically
weighted prime sum, but supplies no error at the square-root scale
needed for Robin. The signed target remains the
[same-source residual](../Analytic/polak2026finiterobinca.md).
This application is a paper derivation with no new Lean declaration or
Lean verification.

## A prime-axis cut of the same actual CA correction

The fixed-window law can be applied to the **actual support primes** of
one strict CA inventory. This is a different observable from the
five-window label of the composite integer itself. Reuse the inventory
and rejected-layer bound in the
[Mertens application](../Weil/broadbent2026mertens.md#fixed-table-upper-allowances-at-the-actual-ca-inventory):

$$
\varepsilon(t)=\frac1{t\log t},\qquad
a_p(t)=\#\{k\ge1:r_{p,k}>\varepsilon(t)\},\qquad
N^-(t)=\prod_p p^{a_p(t)}.
$$

For a label $\sigma\in\{null,2,3,2\ 5,5\}$, put

$$
T_\sigma(t)=
-\sum_{\substack{p:a_p(t)\ge1\\\chi(p)=\sigma}}
\log(1-p^{-a_p(t)-1}).
$$

These are positive contributions of this very inventory, with no
replacement prime law or separately optimized exponent vector. The
partition gives the finite exact equality
$T(t)=\sum_\sigma T_\sigma(t)$, where $T$ is its existing
finite-exponent Euler correction. Let $w_\sigma$ denote the
**unconditional** column of the preceding table. The classical CA
threshold formula and fixed-window prime law yield the application

$$
T_\sigma(t)
=\frac{\sqrt2\,w_\sigma+o(1)}{\sqrt t\log t},
\qquad t\longrightarrow\infty.
\tag{3}
$$

The limit is over all real prices in this clock parametrization,
including tied layer thresholds, and hence also applies along any
unbounded stable self-match roots. It requires only fixed windows.
The ingredients are published CA factorization and prime sampling;
(3) is their attributed same-inventory application, not a new prime
distribution theorem, new Robin coverage or Lean verification.

Here is the parameter and error correspondence. Define, for real
$x>1$,

$$
F(x,k)=\frac{\log(1+(x+\cdots+x^k)^{-1})}{\log x},
\qquad F(x_k(t),k)=\varepsilon(t).
$$

The strict threshold convention is the one in
[Alaoglu–Erdős, §3, Theorem 10](../Arith/alaoglu1944highly.md),
[primary PDF, p.9](https://www.renyi.hu/~p_erdos/1944-03.pdf#page=9):
its brackets mean the greatest integer strictly less than the
argument. In these parameters, $a_p(t)=\#\{k:p<x_k(t)\}$,
so the exponent-one primes are exactly
$x_2(t)\le p<x_1(t)$. The first-layer inequalities already used in
the Mertens application give $t-1<x_1(t)<t$. The fixed second-layer
relation $F(x,2)\sim1/(x^2\log x)$ gives

$$
x_2(t)\sim\sqrt{2t}.
$$

For completeness, $x_2\to\infty$ and the defining relation imply
$x_2^2\log x_2\sim t\log t$. Taking logarithms first gives
$\log x_2/\log t\to1/2$, and substituting back gives
$x_2^2/t\to2$. No prime error or RH assumption is inserted into
this real threshold computation.

For the higher-exponent contributions, the existing rejected next layer
gives $p^{-a_p-1}<3\log p/(t\log t)$. Split those primes at
$t^{1/3}$. Below the split, the bound and ordinary integer counting
give $O(t^{-2/3})$; above it, $a_p\ge2$ gives
$p^{-a_p-1}\le p^{-3}$ and the decreasing integer tail gives the
same bound. Since $p^{-a_p-1}\le1/4$, replacing it by
$-\log(1-p^{-a_p-1})$ changes this estimate by at most a factor
$4/3$. On the exponent-one range, the quadratic remainder in
$-\log(1-p^{-2})=p^{-2}+O(p^{-4})$ totals
$O(x_2^{-3})$. These bounds apply to any of the nonnegative class
subsum contributions and are uniform at events. Consequently

$$
T_\sigma(t)=
\sum_{\substack{x_2(t)\le p<x_1(t)\\\chi(p)=\sigma}}\frac1{p^2}
+O(t^{-2/3}).
\tag{4}
$$

Let $A_\sigma(y)=\#\{p\le y:\chi(p)=\sigma\}$. The fixed-window
law and PNT give $A_\sigma(y)\sim w_\sigma y/\log y$.
Abel summation therefore gives

$$
\sum_{\substack{p\ge y\\\chi(p)=\sigma}}p^{-2}
\sim\frac{w_\sigma}{y\log y}.
$$

The possible endpoint term is $O(y^{-2})$. Subtracting the tail at
$x_1(t)\asymp t$ costs $O(1/(t\log t))$. Inserting
$x_2(t)\sim\sqrt{2t}$ into (4) gives (3), since
$t^{-2/3}=o(1/(\sqrt t\log t))$.

The same argument keeps the unit of each **prime** $p$ and uses the
joint masses of $(h(p),\chi(p))$ in place of $w_\sigma$. Thus the
conditional geometric ratios describe how the actual correction
divides among prime labels after conditioning on $h(p)$. They are
not conditioned on $h(N^-(t))$, and a label of $N^-(t)$ supplies no
such prime-factor condition.

Summing (3) recovers the classical leading correction
$\sqrt2/(\sqrt t\log t)$ because $\sum_\sigma w_\sigma=1$.
This cut identifies the shares of an existing compensation and creates
no extra budget. It gives neither the sign of the same-source Mertens
error nor a lower bound for $I_\psi$ at the root. Those remain the
signed arithmetic obligations in the
[full-support core](../Analytic/polak2026finiterobinca.md#directly-reusable-effective-core).

## Quantitative resolution of the same prime-axis cut

A quantitative input gives an absolute error for this cut and a
sufficient range for increasing its depth. Reuse
[Maynard–Pandey–Radziwiłł, Theorem 1.1](maynardpandeyradziwill2026primes.md)
and its golden-rotation parameter application, together with DMS's
low-address detection. For every fixed $\epsilon>0$, uniformly over
circle intervals $I$,

$$
\#\{p\le X:\{p\varphi\}\in I\}-|I|\pi(X)
=O_\epsilon(X^{19/24+\epsilon}/\log X).
\tag{5}
$$

The same uniform bound applies to a union of at most two circle
intervals. Its centering uses the **actual** $\pi(X)$; no power-saving
estimate for $\pi(X)-\operatorname{Li}(X)$ is inserted. The source
note preserves the harmonic-average denominator bound needed to retain
the $19/24$ exponent and removes proper prime powers before reading
the digits of an actual support prime.

Let $B$ specify a legal prefix of $r\ge1$ consecutive five-mode
windows, after the separate unit digit. Keeping the unit gives DMS
cutoff $3r+3$ and one low address $u$ with interval length

$$
\mu_B\in\{\varphi^{-(3r+1)},\varphi^{-(3r+2)}\}.
$$

If only the unit is forgotten, sum the masses of its admissible unit
choices; the resulting window is a union of at most two circle
intervals and still has $\mu_B\ge\varphi^{-(3r+2)}$. All labels
refer to the digits of the support prime $p$. Define $T_B(t)$ by
restricting the same actual correction $T(t)$ to those support primes.
The previously established higher-exponent estimate and exponent-one
interval give, for every fixed $0<\epsilon<1/24$, with a constant
independent of $B,r,t$,

$$
\boxed{
T_B(t)-\mu_BT(t)
=O_\epsilon\!\left(
\frac{t^{-29/48+\epsilon}}{\log t}+t^{-2/3}
\right).
}
\tag{6}
$$

Indeed, apply (5) to the centered prime counting function and use Abel
summation with $p^{-2}$ over $[x_2(t),x_1(t))$. Its lower endpoint
and integral each cost
$O_\epsilon(x_2^{-29/24+2\epsilon}/\log x_2)$; the upper endpoint
is smaller. The strict endpoints add at most $O(x_2^{-2})$.
Since $x_2\sim\sqrt{2t}$, this is the first error in (6). Subtracting
$\mu_B$ times the total higher-exponent contribution adds only the
already bounded $O(t^{-2/3})$, uniformly over every prefix. The
logarithmic factor's quadratic remainder is smaller as well. The
argument remains valid at tied prices and on all sufficiently large
real $t$, so it also retains every necessary stable root.

Because the existing total satisfies
$T(t)\sim\sqrt2/(\sqrt t\log t)$, (6) yields

$$
\left|\frac{T_B(t)}{\mu_BT(t)}-1\right|
\ll_\epsilon \varphi^{3r+2}
\left(t^{-5/48+\epsilon}+t^{-1/6}\log t\right).
\tag{7}
$$

Consequently, for each fixed $0<\eta<5/48$, choose
$0<\epsilon<\min(\eta,1/24)$. The relative error tends to zero
uniformly over all admissible prefixes with

$$
1\le r\le
\left(\frac5{48}-\eta\right)
\frac{\log t}{3\log\varphi}.
\tag{8}
$$

This is a sufficient resolution range for the **Fibonacci prime-axis
correction**, obtained by transporting the cited estimates. It is not
an optimal depth, a general Pisot growing-block theorem, an effective
numerical starting threshold, or a claim of originality. At a fixed
depth, (6) sharpens only the centered allocation of an existing
correction. Even in the growing range (8), summing the exact class
differences gives zero: the common prime-error mode and the same-root
signed Robin obligation remain unchanged. This paper application has
no new Lean declaration or Lean verification.
