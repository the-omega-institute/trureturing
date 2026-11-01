---
slug: stepanov-herrmann-guhr-2021-correlation-top-eigenvector-weight
bibkey: stepanovherrmannguhr2021correlation
doi: 10.1063/5.0054438
url: https://arxiv.org/abs/2104.08966v1
triage: theorem
motivation_gids:
  - D5/S3/Estimation/CorrelationTopEigenvectorWeight.result
---

# The remaining correlation domain admits the weight gap exactly when $c<\sigma$

## Problem

Y. Stepanov, H. Herrmann and T. Guhr, *Generic features in the spectral decomposition of correlation matrices*, arXiv:2104.08966v1 (Journal of Mathematical Physics 62 (2021), 083505), leave the domain $A\setminus(A_1\cup A_2)$ open. They define
$A=\{(c,\sigma):c>0,\ \sigma>0,\ c^2+\sigma^2<1\}$,
$A_1=\{(c,\sigma)\in A:c\geq\frac12\ \text{or}\ \sigma<c\}$, and
$A_2=\{(c,\sigma)\in A:\sigma>\sqrt3c\ \text{or}\ c<\sigma<1-c\}$.
For an orthonormal eigenbasis, $w_j=\langle v_j,\delta_n\rangle^2$ with $\delta_n=(1,\ldots,1)/\sqrt n$, and the source's definition at TeX lines 877--879 compares $w_1$ with the largest weight among the other eigenvectors. Question III.5 in the source TeX, lines 525--527, asks:

> Given $(c,\sigma) \in A \setminus (A_1 \cup A_2)$ and $n\geq 2$ sufficiently large, is there an $n\times n$ correlation matrix $C$ with mean correlation $c$ and standard deviation $\sigma$ such that $w_1<w_{\max}$ holds?

The formal statement fixes the remaining domain as `domainD` and asks, for every point in it, whether there is a threshold after which every dimension has a correlation matrix with the specified `meanCorr`, `stdCorr`, and `SatisfiesWGap` properties.

## Motivation

The source relates the mean and spread of off-diagonal correlations to the spectral alignment of the leading eigenvector with the normalized all-ones vector. Its results give eventual equality of the leading weight on $A_1$ and construct eventual counterexamples on $A_2$; settling the intervening region determines the exact boundary of that alignment phenomenon under the source's two-characteristic description.

## Gap

The source explicitly says that its $A_1$ and $A_2$ conclusions do not cover $A\setminus(A_1\cup A_2)$ and leaves Question III.5 unanswered. The bounded check recorded in preregistration issue #25287 reports no settlement in the searched scope: Crossref and OpenAlex list no citing works, the later same-group paper by Heckens and Guhr (arXiv:2202.00297) and constant-block correlation results by Roustant and Deville (arXiv:1705.09793) do not answer the question, Zenodo searches returned nothing related, and the repository contained no citation or problem record. This is `not-found-in-searched-scope` rather than an exhaustive literature claim.

## Route

The private lemma `domain_decomposition`, with the sole hypothesis `h : domainD c σ`, proves $0<c<\frac12$, $c\leq\sigma$, and either $\sigma=c$ or $1-c\leq\sigma\leq\sqrt3c$.

For the diagonal case, `small_dimension_obstruction` assumes `hn : n ≤ 2`, a matrix `a`, a real `c`, and `hc : 0 < c`, and proves $\neg(\mathrm{meanCorr}\ a=c\ \land\mathrm{stdCorr}\ a=c)$. For $n\geq3$, `correlation_spectral_data` assumes `hn : 3 ≤ n`, `ha : IsCorrelation a`, `hs : 0 < stdCorr a`, and `hgap : SatisfiesWGap a`; it supplies functions $\mu,w$, an index $i$, zero centered sum $\sum_j\mu_j=0$, energy $\sum_j\mu_j^2=n(n-1)((\mathrm{meanCorr}\ a)^2+(\mathrm{stdCorr}\ a)^2)$, nonnegative weights summing to one, the Rayleigh identity $\sum_j\mu_jw_j=(n-1)\,\mathrm{meanCorr}\ a$, maximality $\forall j,\ \mu_j\leq\mu_i$, and $w_i<\frac12$. The lemma `centered_energy_strict` takes all of those corresponding hypotheses explicitly: `hn : 3 ≤ n`, `hc : 0 < c`, `hμ : ∑ j, μ j = 0`, `henergy : ∑ j, μ j ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (c ^ 2 + σ ^ 2)`, `hw : ∀ j, 0 ≤ w j`, `hsum : ∑ j, w j = 1`, `hrayleigh : ∑ j, μ j * w j = ((n : ℝ) - 1) * c`, an index `i`, `htop : ∀ j, μ j ≤ μ i`, and `hhalf : w i < 1 / 2`; it concludes $c^2<\sigma^2$. Therefore `segment_obstruction`, whose hypotheses are a matrix `a`, `hc : 0 < c`, `ha : IsCorrelation a`, `hm : meanCorr a = c`, and `hs : stdCorr a = c`, proves `¬ SatisfiesWGap a` by using the small-dimensional obstruction or the $n\geq3$ spectral argument.

For $c<\sigma$, `wedge_interval` assumes exactly `h : domainD c σ` and `hcs : c < σ` and proves the four interval facts for
$L=(\sigma^2-(1-c)^2)/(\sigma^2+(1-c)^2)$,
$U=(\sigma^2-c^2)/(c^2+\sigma^2)$, and `wedgeX c σ`: $0\leq L<\mathrm{wedgeX}(c,\sigma)<\min(c,U)<\frac12$. The lemma `wedge_parameters`, with the same two hypotheses, defines $x=\mathrm{wedgeX}(c,\sigma)$, $a=\sigma/\sqrt{1-x^2}$, and $b=c-ax$, and proves $0<x<\frac12$, $x<c$, $a>0$, $b>0$, $1-a-b>0$, and $2c<a+b$.

`rounded_eventually` assumes that exact conjunction for its displayed $x,a,b$ definitions. It gives an $m$ such that every $n\geq m$, with $k=\mathrm{roundedCount}(x,n)$, $z=\mathrm{roundedZ}(n,k)$, $a=\sigma/\sqrt{1-z^2}$, and $b=c-az$, satisfies $3\leq n$, $0<k<n$, $2k\ne n$, $-1<z<1$, $a>0$, $b>0$, $1-a-b>0$, and $2(n-1)c<(n-2)(a+b)$.

The matrix used by `wedge_construction` is `signMatrix n k a b (1 - a - b)`, the sum of a positive diagonal term, a rank-one sign-vector term, and a rank-one all-ones term. `rank_two_realizes` assumes `hn : 3 ≤ n`, `hk : 0 < k`, `hkn : k < (n : ℤ)`, `hσ : 0 < σ`, `hz : -1 < roundedZ n k ∧ roundedZ n k < 1`, the equations `ha : a = σ / Real.sqrt (1 - roundedZ n k ^ 2)` and `hb : b = c - a * roundedZ n k`, and `ha0 : 0 < a`, `hb0 : 0 < b`, `hd0 : 0 < 1 - a - b`; it proves that this matrix is `IsCorrelation` and has `meanCorr` equal to $c$ and `stdCorr` equal to $\sigma$.

The spectral comparison is isolated in `weight_gap`: for a finite index type with decidable equality, functions $\mu,e,s$, positive $a,b$, the diagonal identity
$\mathbf{1}_{i=j}\mu_i=a(s_i s_j)+b(e_i e_j)$,
a strict inequality $2\sum_j\mu_je_j^2<(\sum_j\mu_j)\sum_je_j^2$, an index $i$, and `htop : ∀ j, μ j ≤ μ i`, it produces $j\ne i$ with $e_i^2<e_j^2$. `rank_two_weight_gap` applies this with hypotheses `hn : 3 ≤ n`, `hk : 0 < k`, `hkn : k < (n : ℤ)`, `ha : 0 < a`, `hb : 0 < b`, and
$2(n-1)(a\,\mathrm{roundedZ}(n,k)+b)<(n-2)(a+b)$,
to prove `SatisfiesWGap (signMatrix n k a b d)` for every real `d`. Thus `wedge_construction`, assuming `h : domainD c σ` and `hcs : c < σ`, supplies one common threshold and a realizing matrix in every dimension beyond it. The public theorem `result : claim` combines this construction with `segment_obstruction`.

## Falsifier

The settlement would not answer the source question if the formal predicates changed its quantified problem. Here `IsCorrelation a` is exactly `a.PosSemidef ∧ ∀ i, a i i = 1`; `meanCorr` and `stdCorr` use the strictly lower triangular sums with the displayed real normalization; and `SatisfiesWGap a` quantifies every orthonormal basis and eigenvalue function satisfying the matrix eigen-equations, then every index whose eigenvalue is maximal, requiring a distinct index with strictly larger squared projection on `delta n`. The formal `claim` is the pointwise equivalence for every real $c,\sigma$ satisfying `domainD`, with an existential threshold $m$ and a possibly different matrix for each $n\geq m$. It does not settle the source's $A_1$ or $A_2$ theorems, give an explicit formula for $m$, establish bounds on $\lambda_1$, $w_1$, or $w_{\max}$, or address points outside $A$.

## Evidence

The canonical source is `D5/S3/Estimation/CorrelationTopEigenvectorWeight.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Estimation/CorrelationTopEigenvectorWeight.lean.json`.

Declaration statements:
- `result`: `sha256:ddd7809ea2092d7f1e6123c9fda075889a2dc3086bac95bda4dc40e814c3acab`;
- `claim`: `sha256:400bbd173d1a75d69bdf1f82b06e0a7311d64498cbad9802cbb2bd3a210ffb12`.

- **Proof.** It proves `result : claim`.
- **Axioms.** `#print axioms D5.S3.Estimation.CorrelationTopEigenvectorWeight.result` reports only `propext`, `Classical.choice`, and `Quot.sound`; the source contains no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 question from a 2021 arXiv paper published in *Journal of Mathematical Physics*, preregistered in issue #25287 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every real $c,\sigma$ with `domainD c σ`, there exists $m\in\mathbb N$ such that every $n\geq m$ admits a real $n\times n$ matrix $a$ satisfying `IsCorrelation a`, `meanCorr a = c`, `stdCorr a = σ`, and `SatisfiesWGap a` if and only if $c<\sigma$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- **Mechanism.** On the diagonal $\sigma=c$, a strict weight gap forces the top centered eigenvalue pair to carry enough positive sum that Cauchy--Schwarz makes the centered second moment strictly larger than the value allowed by $\sigma=c$; the obstruction is therefore an energy inequality, rather than a failure of positive semidefiniteness. In the wedge, the rank-two matrix $dI+a ss^{\mathsf T}+b ee^{\mathsf T}$ uses a sign vector and the all-ones vector, with positive coefficients and a limiting parameter chosen inside the interval bounded by $L$, $c$, and $U$. Its two nontrivial spectral directions carry all the weight of the normalized all-ones vector, and the strict half-trace inequality reverses the ordering of the top eigenvalue and its weight.
- **Boundary.** The equivalence is sharp for the formal domain: equality $\sigma=c$ is the obstruction, while every point of the remaining wedge with $c<\sigma$ receives an eventual construction. The theorem supplies existence of a threshold but no quantitative threshold function, and it does not assert uniqueness or optimality of the constructed matrices.
- **Effect on the source.** The source's $A_1$ equality and $A_2$ counterexample results do not use Question III.5 as a premise and remain unaffected. The sentence leaving the intervening domain unanswered is resolved there by the equivalence above; the source's eigenvalue and weight bounds and its discussion of points outside $A$ are outside this settlement.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not establish exhaustive worldwide novelty or priority. The Journal of Mathematical Physics version was not read; only arXiv:2104.08966v1 was read, so preservation of the question in the journal text is unverified. No explicit threshold $m(c,\sigma)$, source result on $A_1$ or $A_2$, bound on $\lambda_1$, $w_1$, or $w_{\max}$, or statement outside $A$ is formalized by `result`.
