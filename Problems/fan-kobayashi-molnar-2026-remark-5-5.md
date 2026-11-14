---
slug: fan-kobayashi-molnar-2026-remark-5-5
bibkey: fankobayashimolnar2025family
doi: 10.1007/s11139-026-01408-3
url: https://arxiv.org/abs/2511.02106v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lemma415
---

# Fan--Kobayashi--Molnar Remark 5.5

## Problem

Fan, Kobayashi and Molnar, *A family of analogues to the Robin criterion*,
Ramanujan Journal 70 (2026), article 40, arXiv:2511.02106v1, discuss in
Remark 5.5 the layer-boundary inequality

$$
x_\ell>x^{1/\ell},\qquad \ell\ge2,
$$

where $x=x_1^{[\kappa]}(\epsilon)$ and the layer variables satisfy
$F^{[\kappa]}(x_\ell,\ell)=\epsilon=F^{[\kappa]}(x,1)$.
The remark states that the authors have been unable to establish this
inequality uniformly in $\ell$. The single assertion considered here is
its layer-base formulation:

$$
\forall\kappa>1\ \exists X\in\mathbb R\ \forall x\ge X\
\forall\ell\in\mathbb N,\ \ell\ge2,\ \forall x'>1:\qquad
F^{[\kappa]}(x',\ell)=F^{[\kappa]}(x,1)\ \Longrightarrow\ x^{1/\ell}<x'.
$$

The threshold may depend on $\kappa$, but must be independent of $\ell$.
Issue [#30215](https://github.com/the-omega-institute/trureturing/issues/30215)
preregisters the comparison and permits this layer-base formulation.

## Motivation

The uniform comparison is the missing layer estimate identified by the
source remark. A threshold for each fixed layer does not imply one
threshold valid for all layers. This assertion isolates that quantifier
gap without requiring an optimal threshold or extending the source
Robin criterion to another parameter range.

## Gap

The source Lemma 4.12 gives the sufficiently-large-base comparison for a
fixed $\kappa>1$ and a fixed layer. The source appendix treats $\kappa=2$.
Neither of those statements supplies the all-layer threshold for every
$\kappa>1$. The theory volume
`docs/develop/theory/LCM_POWER_ROBIN_KAPPA_THRESHOLD.md`, Section 4, gives
an analytic derivation of that threshold. Its recorded literature search
covers the source article, Molnar arXiv:2610.12816v1, and arXiv searches;
that bounded search is not a claim of worldwide priority.

## Route

For $\kappa>1$ define

$$
C(s)=(1+s)^\kappa-s^\kappa,\qquad
B(s)=\log C(s),\qquad \phi(s)=sB'(s).
$$

Concavity of $B$ gives decrease of $B'$ on $(0,\infty)$, and the existing
elasticity result gives strict increase of $\phi$ there. Put

$$
u_0=\max\left(6,\bigl(2^{\kappa+1.01}\bigr)^{1/(\kappa-1)}\right).
$$

For $u\ge u_0$, set $v=2/u$ and $r=2/(u+2)$. The elasticity formula gives
$\phi(v)\ge\kappa(r-r^\kappa)$. The threshold gives
$u^{\kappa-1}\ge2^{\kappa+1.01}>2\cdot2^\kappa$, hence

$$
ur\ge\frac32,\qquad
ur^\kappa\le\frac{2^\kappa}{u^{\kappa-1}}<\frac12,
\qquad u\phi(2/u)>\kappa.
$$

For $n\ge2$ and $0<s\le n/u$, decrease of $B'$ and increase of $\phi$ yield

$$
nB'(s)\ge nB'(n/u)=u\phi(n/u)\ge u\phi(2/u)>\kappa.
$$

Set $y=x^{1/\ell}$, $u=\log x$, $h=y^{-\ell}$ and
$s=(1-h)/(y-1)$. For $x\ge e^{u_0}$, the logarithm bound
$\log y\le y-1$ gives $s\le\ell/u$. The layer factorization gives

$$
\kappa\log y\,F^{[\kappa]}(y,\ell)=B(s)-B(s-h),\qquad
\kappa\ell\log y\,F^{[\kappa]}(y^\ell,1)=B(h).
$$

Concavity gives $B(s)-B(s-h)\ge hB'(s)$, while $B(h)<\kappa h$.
Consequently $\ell(B(s)-B(s-h))>B(h)$, proving the strict comparison
with the specified explicit threshold.

For a natural $n\ge1$, let $S_n(t)=\sum_{j=1}^n t^j$ and $D_n=S_n'$.
Termwise comparison gives $tD_n(t)\le nS_n(t)$ for $t>0$, which implies
$D_{n+1}/S_{n+1}\ge D_n/S_n$. Together with strict increase of $\phi$
and $B'>0$, this makes $B(S_{n+1})-B(S_n)$ strictly increasing and
positive. The case $n=0$ follows from $B'>0$ and $B(0)=0$. Substitution
$t=1/y$ and division by the positive increasing $\kappa\log y$ prove
strict decrease of $F^{[\kappa]}(\cdot,\ell)$ on $(1,\infty)$ for every
$\ell\ge1$, by an independent proof of the natural-layer restriction of source Theorem 4.3. If $x'>1$ and
$F^{[\kappa]}(x',\ell)=F^{[\kappa]}(x,1)$, this strict decrease gives
$x'>x^{1/\ell}$. No inverse-function construction is asserted.

## Falsifier

For a fixed real $\kappa>1$, a proof that for every real $X$ there are
$x\ge X$, a natural $\ell\ge2$ and $x'>1$ with
$F^{[\kappa]}(x',\ell)=F^{[\kappa]}(x,1)$ and $x'\le x^{1/\ell}$ would refute the
assertion. A disagreement between `lcmPowerF` and source Definition 4.2
would invalidate the source correspondence. A finite counterexample
below one chosen threshold would not refute an existence threshold.

## Evidence

The Lean theorem is
`D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_uniform`.
It is the unique terminal settlement result. The intermediate strict F comparison
is `layer_boundary_explicit`, and base monotonicity is `F_strictAntiOn`.
Both are consumed by the explicit equal-value layer-base comparison
`layer_boundary_xl`, which is consumed by `layer_boundary_uniform`.
The existence theorem chooses the same explicit threshold.

These declarations use the existing real-valued `lcmPowerF` definition from
`LcmPowerLemmaFifteen.lean`, the `logPowerDifference` definition and
concavity theorem from `LcmPowerLogConcavity.lean`, and the existing
elasticity monotonicity proof. Its exact statement quantifies a real
threshold before the base and the natural layer index.

The literature identity is the existing note
`Library/ArithSums/fankobayashimolnar2025family.md`, with DOI
`10.1007/s11139-026-01408-3` and the pinned arXiv v1 URL.

## Triage

Lean proved: `layer_boundary_uniform` establishes the complete existence-threshold
layer-base comparison for every real kappa greater than one and every natural layer
at least two, for every base greater than one satisfying the defining F equality.
The existing logarithmic concavity and elasticity monotonicity results supply its analytic prerequisites. `layer_boundary_explicit` gives
$X=\exp(u_0)$ with the stated $u_0$, `F_strictAntiOn` proves strict base
monotonicity for all natural layers at least one, and `layer_boundary_xl`
gives the source layer-base comparison from its defining equality.

Mathematical derivation not formalized here: the theory volume's Remark
4.4 derives that a uniform threshold cannot be $2$ for $1<\kappa<2$, and
that any uniform threshold must diverge as $\kappa\to1^+$. These are
distinct assertions and are not part of this single comparison theorem.
The inverse-function construction of the source layer variables is also
outside the conditional layer-base statement; the equal-value implication uses the independently
proved Lean base monotonicity.

The proved uniform layer estimate supplies the missing sufficiently-large-$x$
step in the Robin route. The source Theorem 5.2 already holds for every
$\kappa>1$; neither its statement nor its parameter range is enlarged by
this result.

Not formalized: the complete alternative proof of that criterion. The
appendix estimate for $E_\kappa(x)$ assumes $\kappa\ge2$, so the layer
comparison alone does not complete the alternative proof for all
$\kappa>1$.

Undecided: the optimal all-layer threshold as a function of $\kappa$.
The other questions in the source Section 8, including its RH implication
for smaller $\kappa$, are outside this delivery; no resolution of them
is claimed here.

## ASSUMED-UNVERIFIED

No new online literature search is asserted. The source correspondence
uses the pinned paper and the existing literature note. The bounded
search recorded in the theory volume does not cover unpublished work or
all later versions. The threshold lower bounds and divergence argument
in Remark 4.4 are mathematical derivations, not Lean conclusions of the
uniform-comparison declaration.
