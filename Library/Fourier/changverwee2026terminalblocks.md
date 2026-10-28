---
bibkey: changverwee2026terminalblocks
authors: Sungkon Chang; Johann Verwee
year: 2026
title: Terminal Blocks of Primes in Pisot Numeration Systems
doi: null
url: https://arxiv.org/abs/2610.10026v1
claim: "Theorems 1.5–1.6 give asymptotic prime frequencies for fixed words of complete semi-proper blocks under the stated Pisot and minimal-polynomial hypotheses. The Zeckendorf unit case is explicitly attributed to DMS detection and classical prime equidistribution; no growing-depth or CA-root Robin estimate is supplied."
strata_touched: []
license: citation-only
triage: anchor
---

# Prime terminal blocks in Pisot numeration

The inspected source is the authors' preprint
[arXiv:2610.10026v1](https://arxiv.org/pdf/2610.10026v1), submitted
7 October 2026. The locators use that version: Theorem 1.1 and its
following attribution on printed p.2; Theorems 1.5–1.6 on printed p.4;
and §2.1's definitions of the coefficient order and semi-proper blocks.
The source statements and their applicability were checked, not the
complete proof. This entry makes no peer-review or Lean-verification
claim.

## Fixed complete-block statement

The paper fixes an order $L\ge2$ and positive integer recurrence data
$g=(1,g_2,\ldots,g_L)$, reverses them to $h_i=g_{L+1-i}$, and uses
its specified initial weights $H_1=1$ and
$H_{r+1}=\sum_{j=1}^r h_jH_{r+1-j}$ for $1\le r<L$.
The later weights satisfy the order-$L$ recurrence. The characteristic
polynomial is

$$
P_h(T)=T^L-h_1T^{L-1}-\cdots-h_{L-1}T-1.
$$

Let $\vartheta>1$ be its dominant root. Theorems 1.5–1.6 assume
that $\vartheta$ is a Pisot number and that $P_h$ is its minimal
polynomial. Coefficient words are read from smaller to larger weights.
Their semi-proper blocks are
$b_{i,j}=(j,h_{i-1},\ldots,h_1)$ for $0\le j<h_i$.
The finite integer's canonical infinite block expansion is eventually
the zero block. These are the paper's numeration conventions; they
must not be replaced silently by a different greedy expansion.

For each fixed positive integer $e$ and each fixed concatenation $B$
of $e$ such complete blocks, the source states

$$
\#\{p\le X:p\text{ prime},\ \operatorname{TB}_e(p)=B\}
\sim\pi(X)\vartheta^{-\operatorname{len}(B)}.
$$

Here $\operatorname{len}(B)$ is its total digit length, and
$\operatorname{TB}_e$ reads the first $e$ blocks from the small-weight
end. A fixed number of complete blocks is not the same condition as
an arbitrary cutoff inside a block, and the statement supplies no
uniform error for $e=e(X)\to\infty$. **§9.2, Problem 1, printed
p.60**, explicitly asks for a uniform law with growing total digit
length; the following paragraph also leaves quantitative error terms
and level of distribution for terminal conditions as further problems.

## Fibonacci conventions and the existing prime-window interface

For $g=(1,1)$ the weights start $H_1=H_2=1$, and the canonical block
language forces the first duplicate unit position to be empty. Thus
the source's blocks $(0)$ and $(0,1)$ include that position; $(0,1)$
must not be reinterpreted as coefficients of $(F_2,F_3)=(1,2)$.
The separate Zeckendorf statement, Theorem 1.1, uses
$F_1=F_2=1$, $a_1=0$, and gives unit-digit masses
$\varphi^{-1}$ for $a_2=0$ and $\varphi^{-2}$ for $a_2=1$.
The paragraph following it explicitly attributes this case to
Drmota–Müllner–Spiegelhofer, Lemma 4.1, and Vinogradov
equidistribution.

The [DMS note](drmotamullnerspiegelhofer2025primes.md#the-actual-five-window-prime-frequencies-and-the-retained-unit)
already records the application to the exact
$[null,2,3,2\ 5,5]$ window, using the original same-integer
rotation intervals and keeping the unit digit. Its distribution
argument is reused; the general Pisot theorem is not required to
reprove the Fibonacci case.

These results sample primes and fixed digit observations. They do not
sample the sparse composite chain of actual colossally abundant
integers, identify their Euler correction from a digit label, or
bound the signed integral in the
[Robin residual](../Analytic/polak2026finiterobinca.md).
The source's **§9.1, printed pp.59–60**, states the corresponding
transfer condition: terminal restrictions can be inserted when the
necessary twisted arithmetic estimates are available; a toral lift
does not remove an already open untwisted problem.

## Möbius weights on fixed complete blocks

The same source already proves a signed arithmetic statement: Corollary 7.11, printed pp.50–51, under Hypothesis 4.3, gives for every fixed depth $e\ge1$ and complete block word $B\in\mathcal B_e$,

$$
\sum_{n\le X}\mu(n)\mathbf1_{\{\operatorname{TB}_e(n)=B\}}=o(X).
$$

Proposition 8.1, printed pp.55–56, proves Hypothesis 4.3 under Assumption 2.8, namely the source's Pisot and minimal-polynomial conditions recorded above. These hypotheses hold for its stated Fibonacci system. The result is reused directly; translating it to the project's five-window vocabulary is not a new Möbius estimate, and the retained unit and complete-block conventions still apply.

The proof uses Davenport's uniform additive-twist estimate $X/(\log X)^A$ for each finite Fourier approximation. Its boundary exceptional set and Riemann-integrable approximation contribute only $o(X)$ in the stated argument. Therefore the corollary does not automatically inherit Davenport's logarithmic rate, a square-root error, or uniformity for depth growing with $X$.

For a fixed $e$, the finite block classes form an exact exhaustive partition of the integers. Hence, writing $M(X)=\sum_{n\le X}\mu(n)$,

$$
M(X)=\sum_{B\in\mathcal B_e}
 \sum_{n\le X}\mu(n)\mathbf1_{\{\operatorname{TB}_e(n)=B\}}.
$$

In particular, square-root bounds $O_\varepsilon(X^{1/2+\varepsilon})$ for every class at even one fixed depth would already imply the ordinary RH-equivalent Mertens bound. Uniform constants over a growing collection of depths are not needed for this implication: the collection at that one depth is finite. The displayed $o(X)$ corollary instead gives the known $M(X)=o(X)$ after summation; the full family of twisted assertions is not identified with that single untwisted consequence. Fixed-resolution geometric refinement has not removed the constant arithmetic component. Growing-depth quantitative control and the Robin residual remain unsupplied.
