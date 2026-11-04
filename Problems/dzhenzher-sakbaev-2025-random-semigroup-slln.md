---
slug: dzhenzher-sakbaev-2025-random-semigroup-slln
bibkey: dzhenzhersakbaev2026slln
doi: 10.1007/s43036-025-00481-7
url: https://arxiv.org/abs/2507.07658v3
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Probability/RandomExponentialProductSLLN.result
---

# The Dzhenzher–Sakbaev random semigroup SLLN holds on every Banach space

## Problem

S. V. Dzhenzher and V. Zh. Sakbaev, *The Strong Law of Large Numbers for random semigroups on uniformly smooth Banach spaces*, arXiv:2507.07658v3 (Advances in Operator Theory 11 (2026), article 4), state Conjecture 2.6 in `mains/slln_smooth.tex`, lines 224–229:

> This leads us to the following conjecture. Let $\mathcal{X}$ be a Banach space. Then under the assumptions of Theorem~\ref{t:slln-sot}, $e^{A_1t/n} \ldots e^{A_nt/n}$ converges a.s. in SOT of $\norm{\cdot}_\mathcal{X}$ to $e^{\Expect At}$ uniformly for $t>0$ in any segment.

The formal declaration `randomProduct` multiplies, in increasing index order, the factors $\operatorname{exp}(((t/n : \mathbb R):\mathbb K)\mathbin{\cdot}a_i(\omega))$ for $i\in\operatorname{Fin}(n)$. The declaration `claim` quantifies over a scalar type $\mathbb K$ with `RCLike`, a normed additive commutative group $e$ with a `NormedSpace` and `CompleteSpace` structure, a measurable type $\alpha$, a probability measure $\mu$, and a sequence $a : \mathbb N\to\alpha\to(e\toL[\mathbb K]e)$. It assumes `AEStronglyMeasurable` for every $a_i$, pairwise `IndepFun`, `IdentDistrib (a_i) (a_0)` for every $i$, and a real $m$ such that $\|a_i(\omega)\|\le m$ almost everywhere for every $i$. For every $x:e$ and $t\ge0$, almost every $\omega$ satisfies: for every $\varepsilon>0$, eventually in $n$ and for every $s\in[0,t]$,

$\left\|\left(\operatorname{randomProduct}(a,n,s,\omega)-\operatorname{exp}\left(((s:\mathbb R):\mathbb K)\mathbin{\cdot}\int z,\,a_0(z)\,d\mu\right)\right)x\right\|<\varepsilon$.

The operator measurable space used by `claim` is the Borel space on $e\toL[\mathbb K]e$, and its algebra structure is `NormedAlgebra.restrictScalars ℝ \mathbb K`.

## Motivation

The source proves the strong-operator law for uniformly smooth Banach spaces and a weak-operator version for Banach spaces, with the strong law on $\ell_1$ obtained from Schur's theorem. Conjecture 2.6 asks whether the strong-operator conclusion extends to every Banach space under the same bounded i.i.d. semigroup assumptions. The formal statement removes the uniform-smoothness restriction while retaining the measurable, independent, identically distributed, and common almost-sure boundedness hypotheses.

## Gap

The literature check recorded in preregistration issue [#22585](https://github.com/the-omega-institute/trureturing/issues/22585) found the conjecture in arXiv v3 and no settlement in the searched scope. The issue records that the authors' follow-up arXiv:2601.04612v2 treats unbounded generators on uniformly smooth spaces, not this conjecture, and that Anshelevich and Nguyen, *Convergence of permuted products of exponentials* (arXiv:2504.02681), studies related Banach-algebra products without stating the i.i.d. random-operator conjecture. It also records site-restricted searches of Zenodo, ResearchGate, SSRN, and GitHub with no settlement and no prior repository record.

`not-found-in-searched-scope`.

## Route

1. In the non-subsingleton branch of `operator_uniform_to_sot`, set $b=\int z,\,a_0(z)\,d\mu$. From `AEStronglyMeasurable (a 0)` and the almost-everywhere bound `ha 0`, `Integrable.of_bound` supplies integrability; the existence of a point in the bound gives $0\le m$, and `norm_integral_le_of_norm_le_const` gives $\|b\|\le m$. `ProbabilityTheory.strong_law_ae a hint hind hid`, with the exact pairwise-independence hypothesis `hind` and identical-distribution hypothesis `hid` under the Borel operator space, yields convergence of the normalized sums to $b$. `centered_max_sublinear` applies to any `NormedAddCommGroup e` with `NormedSpace ℝ e` when the exact hypothesis is `Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i) atTop (𝓝 b)`: for every $\varepsilon>0$ it gives eventually in $n$ the bound $\|\operatorname{centeredSum}(a,b,k)\|\le\varepsilon n$ for every $k\le n$.
2. The algebraic part uses `euler_succ` for the exact recursion of `eulerProduct`, and `abel_step` for the noncommutative summation-by-parts identity; these require respectively `[Ring e] [Module ℝ e]` and `[Ring e] [Algebra ℝ e]`. `ordered_norm` requires `[NormedRing e] [NormOneClass e]` and hypotheses $\|a_i\|\le l$ for every $i<n$, and gives the product norm bound $l^n$. `euler_norm`, under `[NormedRing e] [NormedAlgebra ℝ e] [NormOneClass e]`, $0\le m$, $0\le h$, and $\|a_i\|\le m$ for $i<n$, bounds the Euler product by $(1+hm)^n$.
3. `euler_abel_bound`, under `[NormedRing e] [NormedAlgebra ℝ e] [NormOneClass e]`, $0\le m$, $0\le h$, $0\le r$, $\|a_i\|\le m$ for $i<n$, $\|b\|\le m$, and $\|\operatorname{centeredSum}(a,b,k)\|\le r$ for every $k\le n$, gives
   $\|\operatorname{eulerProduct}(a,h,n)-(1+h\mathbin{\cdot}b)^n\|\le h\exp(hmn)(1+2hmn)r$.
   `ordered_perturbation`, under `[NormedRing e] [NormOneClass e]`, $1\le l$, $0\le d$, and the exact hypotheses $\|a_i\|\le l$, $\|b_i\|\le l$, and $\|a_i-b_i\|\le d$ for every $i<n$, controls the difference of their products by $n d l^n$.
4. `exp_euler_remainder`, under `[NormedRing e] [NormedAlgebra ℝ e] [NormOneClass e] [CompleteSpace e]`, assumes $0\le r$, $\|z\|\le r$, and $r\le1$, and bounds $\|\operatorname{exp}z-(1+z)\|$ by $(3/4)r^2$. `exponential_euler_bound`, under those same four typeclass hypotheses, assumes $0\le m$, $0\le t$, $0<n$, $\|a_i\|\le m$ for $i<n$, and $t/n\mathbin{\cdot}m\le1$, and bounds the exponential product minus the Euler product by $(3/4)m^2t^2\exp(mt)/n$. These estimates and `euler_abel_bound` are assembled by `deterministic_uniform`: under `[NormedRing e] [NormedAlgebra ℝ e] [NormOneClass e] [CompleteSpace e]`, $0\le m$, the pointwise bound $\|a_i\|\le m$ for every $i$, $\|b\|\le m$, and the exact normalized-sum hypothesis `Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i) atTop (𝓝 b)`, every $t\ge0$ and $\varepsilon>0$ have an eventual $n$ for which the operator norm of the exponential product minus $\operatorname{exp}(s\mathbin{\cdot}b)$ is $<\varepsilon$ for all $s\in[0,t]$.
5. `operator_uniform_to_sot` has `[RCLike 𝕜] [NormedAddCommGroup e] [NormedSpace 𝕜 e] [CompleteSpace e] [MeasurableSpace α]`, a probability measure $\mu$, a sequence $a : ℕ\to\alpha\to e\toL[𝕜]e$, `hsm : ∀ i, AEStronglyMeasurable (a i) μ`, `hind : letI : MeasurableSpace (e\toL[𝕜]e) := borel (e\toL[𝕜]e); Pairwise (fun i j => IndepFun (a i) (a j) μ)`, `hid : letI : MeasurableSpace (e\toL[𝕜]e) := borel (e\toL[𝕜]e); ∀ i, IdentDistrib (a i) (a 0) μ μ`, and a real $m$, and `ha : ∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m`. It handles the `Subsingleton e` case directly. In the nontrivial case it applies `deterministic_uniform` on the full-measure event supplied by `strong_law_ae` and the simultaneous bound `ae_all_iff.mpr ha`; the operator inequality is converted to the required vector inequality using `u.le_opNorm x`. The theorem `result` installs the restricted-scalar algebra and Borel operator measurable-space instances and applies `operator_uniform_to_sot` to prove `claim`.

## Falsifier

A counterexample satisfying the exact `claim` hypotheses—`AEStronglyMeasurable`, pairwise `IndepFun`, `IdentDistrib` with `a 0`, one common real almost-sure bound $m$, and a probability measure—while violating the eventual estimate for some $x$, nonnegative $t$, or $s\in[0,t]$ would falsify the settled proposition. A formal mismatch would have the same effect: changing the left-to-right increasing-index product, either scalar cast, the Borel operator measurable space, the Bochner integral of `a 0`, or the quantifier order would no longer settle the source question represented by `claim`. The statement does not quantify over negative times, unbounded operators, non-identically distributed sequences, rates, or a single event simultaneously for all $x$ and $t$.

## Evidence

The canonical source is `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Analytic/Probability/RandomExponentialProductSLLN.lean.json`.

Declaration statements:
- `result`: `sha256:45288c6e63407fe160c1fd419cbf1cbf7afbbb737c97487979f36eda8963deed`;
- `claim`: `sha256:0a2a90179769d294ab6ef53e0f496bf4d1ff11842305419bb0a57aeb3e1cad70`.

- **Proof.** `result : claim` invokes the private `operator_uniform_to_sot` route described above, including the subsingleton branch, the Banach-valued strong law, and the deterministic uniform estimate.
- **Axioms.** `#print axioms D5.S3.Analytic.Probability.RandomExponentialProductSLLN.result` reports only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture stated in a 2025 paper, preregistered in issue #22585 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every scalar type $\mathbb K$ with `RCLike`, every complete normed additive commutative group $e$ with its `NormedSpace` structure, every measurable type $\alpha$, every probability measure $\mu$, and every sequence $a : \mathbb N\to\alpha\to(e\toL[\mathbb K]e)$ satisfying the exact strong-measurability, pairwise-independence, identical-distribution, and common almost-sure bound hypotheses of `claim`, every $x:e$ and $t\ge0$ satisfy the displayed almost-everywhere eventual estimate uniformly for $s\in[0,t]$.

**Computed, not formalized:** No numerical or counterexample computation is recorded for this settlement, so no additional computed range or value is asserted.

**Argued, not formalized.** The decisive mechanism is the Banach-valued strong law for the operator sequence together with the deterministic Euler comparison: under the strong-measurability, pairwise-independence, identical-distribution, and common almost-sure bound hypotheses of `claim`, centered partial sums become sublinear on every prefix, the noncommutative product perturbation is controlled, and the Taylor and product perturbation errors are of order $1/n$. This explains why the formal result needs a common almost-sure bound and identical independent factors, but it is an explanation of the compiled proof rather than an additional public declaration. The proof has no uniform-smoothness premise, so the exact formal scope includes instances of the source's uniformly smooth and $\ell_1$ settings that meet the Lean hypotheses; it does not establish a weakened boundedness assumption, non-i.i.d. sequences, unbounded generators, convergence rates, or uniformity over all time intervals at once; sharpness of the common bound and of the proof constants is not settled. The private deterministic estimate is in operator norm, while the public declaration `result` settles only the vector-valued SOT statement `claim`; no separate operator-norm theorem is asserted. The source's already stated uniformly smooth SOT and all-Banach WOT results remain source statements; this module addresses the conjecture's all-Banach SOT extension and does not formalize those other source theorems or consequences for the authors' unbounded follow-up.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in issue #22585 and does not establish exhaustive worldwide novelty or priority. The issue's assessment of arXiv:2601.04612v2, the related Anshelevich–Nguyen paper, and its site-restricted searches remains unverified. The correspondence between the source's prose definitions of complete probability spaces, Bochner measurability, random generators, and semigroup notation and the Lean typeclass encoding is not separately formalized beyond the compiled `claim` and `result`. The source's Theorems 2.4 and 2.5, the unbounded-generator follow-up, and the related literature are not formalized in this module. Numerical sharpness and counterexample-search claims remain unverified.
