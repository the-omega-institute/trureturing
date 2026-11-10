---
slug: porto-et-al-2024-n-cycle-nonlocality-contextuality-tradeoff
bibkey: portoetal2024tradeoffnonlocalitycontextuality
doi: 10.1088/1367-2630/ad7167
url: https://arxiv.org/abs/2405.02964v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result
---

# The normalized nonlocality–contextuality trade-off holds for every binary n-cycle

## Problem

L. E. A. Porto, G. Ruffolo, R. Rabelo, M. Terra Cunha and P. Kurzyński, “Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios”, *New Journal of Physics* 26, 083028 (2024), arXiv:2405.02964v2, states the following conjecture in `final_version.tex`, lines 373–375:

> Consider a bipartite generalized Bell scenario where Bob has an $n$-cycle contextuality setup. For any normalized generalized-Bell inequality $S_{GBell}$ and any normalized noncontextuality inequality $S_{NC}$ of Bob's local experiment, every $\mathcal{NSND}$ behavior satisfies expression (12).

The compiled formalization fixes `Behavior n` to `Fin 2 → Fin n → Bool → Bool → Bool → ℝ`, `BobBehavior n` to `Fin n → Bool → Bool → ℝ`, and `AliceResponse` to `Fin 2 → Bool → ℝ`. `IsNSND p` imposes nonnegativity, normalization in every Alice setting and cyclic Bob context, equality of the shared Alice–Bob marginal in consecutive contexts, independence of Bob's marginal from Alice's setting, and independence of Alice's marginal from Bob's context. `IsGeneralizedLocal` is the real convex hull of products of a row-stochastic Alice response with an `IsND` Bob behavior, and `IsNoncontextual` is the real convex hull of deterministic global Boolean assignments. The formal claim is: for every $n$ with $3 \le n$, every $f$ of type `((Behavior n →ₗ[ℝ] ℝ) × ℝ)` and every $t$ of type `((BobBehavior n →ₗ[ℝ] ℝ) × ℝ)` satisfying `IsNormalizedGBell f` and `IsNormalizedNC t`, and every $p$ satisfying `IsNSND p`,
$$
f.1(p)+f.2+\bigl(t.1(\operatorname{bobMarginal}(p))+t.2\bigr)\le 1.
$$

## Motivation

The paper proves this normalized trade-off by enumerating the nonsignaling-and-nondisturbing polytope only for $n=3,4,5$, and then conjectures the all-$n$ statement. An all-cycle result identifies the geometric reason that a contextuality violation consumes the same unit budget that otherwise permits a generalized Bell violation. The formal statement concerns binary tables with two Alice settings and makes no quantum-realizability assumption.

## Gap

The bounded literature check recorded in issue [#24437](https://github.com/the-omega-institute/trureturing/issues/24437) found that the source's arXiv v2 and published version retain the all-$n$ conjecture. The issue records a search of four citing works listed by Semantic Scholar without a settlement of this trade-off, and searches of the title, authors, n-cycle and trade-off terms found no other settlement in the searched scope. The cycle-polytope vertices and the midpoint ingredient were known ingredients already used by the source, but no prior theorem found in that check supplied the all-$n$ trade-off. The repository had no prior Problem, Library or D5 record for this source.

`not-found-in-searched-scope`.

## Route

1. From `hp : IsNSND p`, `bob_nd` proves `IsND (bobMarginal p)`. With `hα : IsRowStochastic α` and `hr : IsND r`, `product_nsnd` proves `IsNSND (productBehavior α r)`; independently, `vertex_nd` proves `IsND (vertex γ)` for every Boolean edge-sign vector $\gamma$.

2. For an edge-sign vector $\gamma$ with $\sum_i\gamma_i=\mathrm{false}$, `even_signs_assignment` constructs a global assignment $s$ with $\operatorname{xor}(s_i,s_{\operatorname{finRotate}(n,i)})=\gamma_i$ for every $i$, and `even_vertex_noncontextual` uses that assignment to prove `IsNoncontextual (vertex γ)`. For $n$ with $3\le n$, `cycle_generators` takes any $r$ with `IsND r` and proves $r\in\operatorname{convexHull}(\mathrm{generators}\ n)$, where the generators are deterministic tables and the odd-sign vertices.

3. If odd-sign vectors $\gamma,\eta$ are distinct, `midpoint_noncontextual` proves `IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η)` under the hypotheses `oddSigns γ`, `oddSigns η` and $\gamma\ne\eta$. Given
`hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n)` and
`hmid : ∀ γ η : Fin n → Bool, oddSigns γ → oddSigns η → γ ≠ η → IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η)`, together with a pair $t$ with `IsNormalizedNC t`, `unique_positive_generator` produces an odd-sign $\gamma$ with
$t.1(\operatorname{vertex}\gamma)+t.2=1$ and proves that every odd-sign $\eta\ne\gamma$ has $t.1(\operatorname{vertex}\eta)+t.2\le0$.

4. Given `r : BobBehavior n`, `hr : r ∈ convexHull ℝ (generators n)`, a pair $t$ with `ht : IsNormalizedNC t`, an odd-sign $\gamma$ with `hmax : t.1 (vertex γ) + t.2 = 1`, and `hother : ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0`, `generator_dominance` produces $v\ge0$ with $t.1(r)+t.2\le v$ and $v\,\operatorname{vertex}\gamma(i,b,c)\le r(i,b,c)$ at every coordinate.

5. For `p : Behavior n` with `hp : IsNSND p`, an arbitrary $i_0:\mathrm{Fin}\ n$, Alice setting $x:\mathrm{Fin}\ 2$, outcome $a:\mathrm{Bool}$, `hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n)`, a pair $t$ with `ht : IsNormalizedNC t`, an odd-sign $\gamma$ with the displayed `hmax`, and the displayed `hother`, `slice_dominance` applies the previous result to the slice $q(i,b,c)=p(x,i,a,b,c)$. It returns $w\ge0$ with
$t.1(q)+(\sum_b\sum_c p(x,i_0,a,b,c))t.2\le w$
and $w\,\operatorname{vertex}\gamma(i,b,c)\le p(x,i,a,b,c)$ for all coordinates. Using `hn : 3 ≤ n`, the same $hgen$, `p`, `hp`, $t$, `ht`, a positive contextuality value $c=t.1(\operatorname{bobMarginal}p)+t.2>0$, the same maximizing $\gamma$ and `hother`, `common_local_part` sums the slice conclusions and returns a row-stochastic $\alpha$ satisfying
$c\bigl(\alpha(x,a)\operatorname{vertex}\gamma(i,b,c)\bigr)\le p(x,i,a,b,c)$
for every $x,i,a,b,c$.

6. Finally, `dominated_local_tradeoff` assumes `IsNSND p`, `IsNSND l`, `IsGeneralizedLocal l`, $0<c$, $c\le1$, and coordinatewise domination $c\,l\le p$. For `IsNormalizedGBell f`, it proves $f.1(p)+f.2\le1-c$. In `result`, if $c\le0$ the upper-bound clause of `IsNormalizedGBell f` gives $f.1(p)+f.2\le1$ directly. If $c>0$, `unique_positive_generator`, `common_local_part`, `product_nsnd`, `vertex_nd` and the convex-hull definition give the required generalized-local product $l$ and domination; `IsNormalizedNC t` supplies $c\le1$, so `dominated_local_tradeoff` gives the complementary Bell bound, and the two bounds yield the formal inequality.

## Falsifier

The settlement would not address the source conjecture if the formal tables or normalization predicates differed from the stated binary cycle model. In particular, `Behavior n` has exactly two Alice settings and three Boolean outcome coordinates, `IsNSND` uses the cyclic `finRotate` shared-marginal equation and both nonsignaling marginal equations, and `bobMarginal` is read at Alice setting zero. The two normalized inequalities are pairs of a real linear map and offset: `IsNormalizedGBell` is nonpositive on `IsGeneralizedLocal` tables, at most one on every `IsNSND` table, and attained at one `IsNSND` table; `IsNormalizedNC` is nonpositive on `IsNoncontextual` Bob tables, at most one on Bob marginals of `IsNSND` tables, and attained there. A claim for more Alice settings, a different compatibility graph, a quantum subset, or the Peres–Mermin square would be a different proposition.

## Evidence

The canonical source is `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.lean.json`.

Declaration statements:
- `result`: `sha256:137f8b3e3f236d9ec0af64730543205fe37bcd1b35bc77ed1029d65f39843e5a`;
- `claim`: `sha256:f957b3179d25ffeea4c82ca615a9bd6bd2967ffe2a7dbf23184101c2c0ae8692`.

- **Proof.** The module declares `result : claim` and its proof compiles.
- **Axioms.** `#print axioms D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.result` reports `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide` or new axiom.

## Triage

Tier 1 conjecture of a 2024 article, preregistered in issue #24437 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every $n$ with $3\le n$, every affine pair $f$ and $t$ of the exact types in `claim` satisfying `IsNormalizedGBell f` and `IsNormalizedNC t`, and every `IsNSND` behavior $p$, the compiled inequality
$f.1(p)+f.2+\bigl(t.1(\operatorname{bobMarginal}(p))+t.2\bigr)\le1$
holds.

**Computed, not formalized**. None.

**Argued, not formalized.**
- The formal mechanism has the geometric interpretation that the nondisturbing cycle polytope is generated by deterministic tables together with odd-sign vertices, and that the unique maximizing odd vertex provides the common generalized-local part used to pay for the contextuality value; this interpretation adds no statement beyond the named Lean lemmas.
- Sharpness of the numerical bound is open: `result` proves the upper bound but does not assert that equality is attained for every $n$ or for every normalized pair.
- The source's statement that maximal contextuality implies locality, its quantifier reformulations of the trade-off, and its no-joint-witness consequence are not declarations of this module. Their instantiations for the formal binary cycle model remain open here.
- Whether an analogous trade-off holds with more than two Alice measurements or for other compatibility structures is open. The Peres–Mermin-square counterexample discussed by the source lies outside this statement.
- Quantum behaviors of the binary cycle scenario are nonsignaling and nondisturbing, so `result` bounds every quantum behavior once it is shown to satisfy `IsNSND`; no formal bridge from quantum models to `IsNSND` is included here. A variant that normalizes the inequalities by their maxima over the quantum set rather than over the NSND set is a different question and is not settled here.

The source's other results that use the trade-off can use this settlement only after matching these formal hypotheses. The source's Result 2, quantifier versions, Peres–Mermin analysis and quantum-realizability claims are not formalized by `result`; no conclusion about them is emitted here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the citing-work reading recorded in issue #24437 was not independently reproduced. The n-cycle generator and midpoint ingredients used by the module are formalized in the exact forms named in `Route`, but their broader literature attributions were not independently checked here. The source's quantifier formulations, no-joint-witness result, maximal-contextuality-implies-local statement, Peres–Mermin example and quantum-realizability discussion are not formalized. No claim is made here about scenarios outside the binary two-setting cycle model.
