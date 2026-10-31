---
slug: porto-et-al-2024-n-cycle-nonlocality-contextuality-tradeoff
bibkey: portoetal2024tradeoffnonlocalitycontextuality
doi: 10.1088/1367-2630/ad7167
url: https://arxiv.org/abs/2405.02964v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result
---

# The Porto–Ruffolo–Rabelo–Terra Cunha–Kurzyński n-cycle trade-off holds for every binary cycle

## Problem

L. E. A. Porto, G. Ruffolo, R. Rabelo, M. Terra Cunha and P. Kurzyński, *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*, New J. Phys. 26, 083028 (2024), arXiv:2405.02964v2, state the following conjecture in `final_version.tex`, lines 373–375:

> Consider a bipartite generalized Bell scenario where Bob has an $n$-cycle contextuality setup. For any normalized generalized-Bell inequality $S_{GBell}$ and any normalized noncontextuality inequality $S_{NC}$ of Bob's local experiment, every $\mathcal{NSND}$ behavior satisfies expression \eref{eq: trade-off_inequalities}.

The formal statement fixes $n\ge3$. It represents a behavior by $Behavior(n)=Fin 2\to Fin n\to Bool\to Bool\to Bool\to ℝ$, a Bob table by $BobBehavior(n)=Fin n\to Bool\to Bool\to ℝ$, and an Alice response by $Fin 2\to Bool\to ℝ$. `IsAliceResponse` requires nonnegative entries and unit sum for each Alice setting. `IsND` requires nonnegative, normalized context tables and equality of the shared-measurement marginals in consecutive contexts. `IsNSND` requires nonnegativity, normalization, the shared Alice/shared-Bob marginal equality, independence of Bob's marginal from Alice's setting, and independence of Alice's marginal from Bob's context. `bobMarginal` sums over Alice's outcome at setting $0$.

`IsGeneralizedLocal` is the real convex hull of products of an `IsAliceResponse` and an `IsND` Bob table. `IsNoncontextual` is the real convex hull of the tables `deterministic s` for Boolean global assignments $s:Fin n\to Bool$. `IsNormalizedGBell f` says that the affine value $f.1(p)+f.2$ is nonpositive on generalized-local tables, at most $1$ on every `IsNSND` table, and equal to $1$ for some `IsNSND` table. `IsNormalizedNC t` gives the analogous noncontextual bound and an attained value $1$ on a Bob marginal of an `IsNSND` table.

Thus `claim` says that for every such $n$, every normalized pair $f,t$, and every `IsNSND p`, $f.1(p)+f.2+(t.1(bobMarginal(p))+t.2)\le1$.

## Motivation

The source's normalized values measure generalized Bell nonlocality and Bob's local Kochen–Specker contextuality on the same nonsignaling-and-nondisturbing behavior. A bound on their sum gives a common resource constraint for the binary two-setting generalized Bell scenarios, extending the source's explicit $n=3,4,5$ result to all cycle lengths covered by the formal statement.

## Gap

The bounded check recorded in issue [#24437](https://github.com/the-omega-institute/trureturing/issues/24437) found no settlement in its searched scope:

- arXiv v2 and the published article retain the all-$n$ conjecture.
- The citing works listed there do not settle this trade-off; the checked papers on global contextuality and coordination cost address different statements.
- The earlier $n$-cycle vertex description and the midpoint fact are ingredients of the source, but no theorem found in the check supplied the all-$n$ trade-off.
- The repository search found no prior `Problems/`, `Library/`, or `D5/` settlement for this source.

`not-found-in-searched-scope`.

## Route

The proof uses the following lemmas with their stated hypotheses.

1. `bob_nd` turns `hp : IsNSND p` into `IsND (bobMarginal p)`. It obtains nonnegativity from the Alice-$0$ slice, normalization by summing the `IsNSND` normalization, and nondisturbance from the shared-marginal condition.
2. `product_nsnd` proves `IsNSND (productBehavior α r)` from `hα : IsAliceResponse α` and `hr : IsND r`.
3. `even_signs_assignment` says that, for `γ : Fin n → Bool` with `∑ i, γ i = false`, there is an assignment $s$ whose consecutive Boolean xors equal $γ$. `even_vertex_noncontextual` then proves `IsNoncontextual (vertex γ)` under the same parity hypothesis.
4. `cycle_generators` assumes `hn : 3 ≤ n`, a Bob table $r$, and `hr : IsND r`; it proves that $r$ lies in the convex hull of all deterministic tables and all `vertex γ` tables with odd sign product. Even-parity vertices are replaced using `even_vertex_noncontextual`.
5. `midpoint_noncontextual` assumes odd-sign patterns `γ` and `η` with `γ ≠ η`; it proves that the midpoint of `vertex γ` and `vertex η` is `IsNoncontextual`.
6. `unique_positive_generator` assumes a generator-hull property for every `IsND` table, the midpoint property from step 5, a functional pair `t`, and `ht : IsNormalizedNC t`. It produces an odd pattern `γ` with affine value exactly $1$ and proves that every other odd pattern has affine value at most $0$.
7. `generator_dominance` assumes that an `IsND` table $r$ is in the generator convex hull, a functional pair `t` with `ht : IsNormalizedNC t`, the maximizing equality for `γ`, and the non-maximizer bound for every other odd pattern. It produces $v\ge0$ with affine value at most $v$ and the coordinatewise domination $v\,vertex(γ)(i,b,c)\le r(i,b,c)$.
8. `slice_dominance` assumes the generator-hull property, a behavior `p` with `hp : IsNSND p`, an index `i₀ : Fin n`, Alice indices `x` and `a`, a functional pair `t` with `ht : IsNormalizedNC t`, the maximizing `γ`, and the other-generator bound. It produces $w\ge0$ bounding the affine value of the subnormalized slice $p(x,i,a,\cdot,\cdot)$, together with coordinatewise domination by $w\,vertex(γ)$.
9. `common_local_part` assumes `hn : 3 ≤ n`, the generator-hull property, a behavior `p` with `hp : IsNSND p`, a functional pair `t` with `ht : IsNormalizedNC t`, a strictly positive contextuality value $t.1(bobMarginal(p))+t.2$, the maximizing `γ`, and the other-generator bound. It produces an `IsAliceResponse α` such that the product $α(x,a)\,vertex(γ)(i,b,c)$, scaled by that contextuality value, is coordinatewise dominated by $p$.
10. `dominated_local_tradeoff` assumes behaviors `p` and `l`, `hp : IsNSND p`, `hl : IsNSND l`, `hloc : IsGeneralizedLocal l`, a coefficient $c$ with $0<c$ and $c\le1$, and coordinatewise domination $c\,l\le p$, a functional pair `f`, and `hf : IsNormalizedGBell f`; it proves $f.1(p)+f.2\le1-c$.
11. `result` takes `n` with `hn : 3 ≤ n`, functional pairs `f` and `t` with `hf : IsNormalizedGBell f` and `ht : IsNormalizedNC t`, and `p` with `hp : IsNSND p`; it splits on whether $t.1(bobMarginal(p))+t.2\le0$. In that branch `IsNormalizedGBell` gives $f.1(p)+f.2\le1$. In the positive branch it applies `cycle_generators`, `midpoint_noncontextual`, `unique_positive_generator`, `common_local_part`, and `dominated_local_tradeoff`, then adds the positive contextuality value to obtain the claim.

## Falsifier

The settlement would not answer the source conjecture if the compiled definitions changed its quantifiers or scenario. A mismatch would include a non-binary outcome alphabet, a number of Alice settings other than `Fin 2`, contexts other than $\{i,\operatorname{finRotate}(n,i)\}$, a different nonsignaling or nondisturbance condition, generalized locality requiring Bob's hidden table to be noncontextual, or a normalization that did not require the two attained maxima. It would also fail to settle the conjecture if `result` proved only a fixed cycle length or only an inequality for a restricted class of $f$ or $t$.

## Evidence

The canonical source is `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.lean.json`.

Declaration statements:
- `result`: `sha256:137f8b3e3f236d9ec0af64730543205fe37bcd1b35bc77ed1029d65f39843e5a`;
- `claim`: `sha256:f957b3179d25ffeea4c82ca615a9bd6bd2967ffe2a7dbf23184101c2c0ae8692`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2024 article, preregistered in issue #24437 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every natural $n$ with $3\le n$, every pair $f\in((Behavior(n)→ₗ[ℝ]ℝ)\timesℝ)$ and $t\in((BobBehavior(n)→ₗ[ℝ]ℝ)\timesℝ)$ satisfying `IsNormalizedGBell f` and `IsNormalizedNC t`, and every `IsNSND p`, the exact inequality $f.1(p)+f.2+(t.1(bobMarginal(p))+t.2)\le1$ holds.

**Computed, not formalized**. None.

**Argued, not formalized.**

- **Mechanism.** `bob_nd` transfers every NSND behavior to a nondisturbing Bob table. `cycle_generators` supplies deterministic and edge-sign generators, `even_vertex_noncontextual` removes even-parity vertices, and `midpoint_noncontextual` makes the midpoint of any two distinct odd vertices noncontextual. `unique_positive_generator` therefore isolates an odd vertex with contextuality value $1$ while all other odd vertices have value at most $0$. When the Bob contextuality value $c=t.1(bobMarginal(p))+t.2$ is positive, `slice_dominance` and `common_local_part` construct a generalized-local product dominated by $p$ after scaling by $c$; `dominated_local_tradeoff` then gives the Bell value at most $1-c$, which is the decisive trade-off step. This description follows the named lemmas but is not a separate Lean declaration.
- **Range.** The formal result covers every finite $n\ge3$, all real linear functionals with real offsets satisfying the two normalization predicates, and all real probability tables satisfying the module's binary `IsNSND` conditions. It does not formalize quantum realizability, more than two Alice settings, nonbinary outcomes, the Peres–Mermin square, or the source's quantifier versions.
- **Sharpness and neighbours.** The declaration proves the upper bound and does not prove a matching equality construction or a separate sharpness theorem. The source's separate statement that maximal contextuality implies locality, its quantifier-based trade-off statements, and broader scenarios remain open here because they are not declarations of this module.

The source's earlier $n=3,4,5$ trade-off result remains a special case of the formal range. The source's other conclusions about quantum realizations, quantifier versions, and scenarios outside the binary two-setting $n$-cycle are unaffected in status: `result` does not formalize them.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and citing works recorded in issue #24437; it does not establish exhaustive worldwide novelty or priority. The source's broader scenario claims, quantum realizability, quantifier versions, matching sharpness, and the separate maximal-contextuality locality statement are not formalized by `result`. The route explanation and the source interpretation were read from the module, Blueprint, library note, issue, and the cited TeX; no additional reading beyond those materials is asserted.
