---
slug: galvao-brod-2020-overlap-interval-propagation
bibkey: galvaobrod2020overlaps
doi: 10.1103/PhysRevA.101.062110
url: https://arxiv.org/abs/1902.11039v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.result
---

# Three-state overlap interval propagation is not always optimal

## Problem

E. F. Galvão and D. J. Brod, *Quantum and classical bounds for two-state overlaps*, Phys. Rev. A 101, 062110 (2020), arXiv:1902.11039v3, Section II.B, `overlap_pra_v3.tex`, line 165:

> We leave it as an open question whether this procedure is optimal, but emphasize that even the initial iteration that produces a complete graph already provides bounds for every pair of vertices, which may be useful even if not tight.

The procedure is specified at lines 151–156: use the three-state bounds through each common neighbour of an unmeasured pair, intersect the inferred intervals, add the edge, and continue. Line 165 also allows revisiting inferred edges. The source's definitions and bounds are at lines 97–131; see [the literature note](../Library/Observer/galvaobrod2020overlaps.md).

Issue [#23699](https://github.com/the-omega-institute/trureturing/issues/23699) fixes the reading to graphs with exactly one unknown pair. Write
$U(x,y)=(\sqrt{xy}+\sqrt{(1-x)(1-y)})^2$, and let $L(x,y)=(\sqrt{xy}-\sqrt{(1-x)(1-y)})^2$ when $x+y>1$, and $L(x,y)=0$ otherwise. These are the module's `upper` and `lower`.

For $m$ labelled states, distinct indices $i_0,j_0$, and an array $r$, a realization is a family of unit vectors $\psi_i\in\mathbb C^n$ satisfying $|\langle\psi_i,\psi_j\rangle|^2=r_{ij}$ for every ordered pair of distinct indices except the unordered pair $\{i_0,j_0\}$. Diagonal entries impose no conditions. The set $F$ of feasible unknown overlaps ranges over every finite dimension $n$. The procedure's endpoints are
$\ell=\sup\{L(r_{ki_0},r_{kj_0}):k\ne i_0,j_0\}$ and $u=\inf\{U(r_{ki_0},r_{kj_0}):k\ne i_0,j_0\}$, encoded by `procLower` and `procUpper`.

The proposition `claim` asserts that, for every $m\ge3$, every distinct $i_0,j_0$, and every $r$ with $F\ne\varnothing$, both $\ell=\inf F$ and $u=\sup F$. This universal tightness statement is refuted.

## Motivation

Inferring unmeasured overlaps from measured ones is the paper's organizing problem. Section IV.B applies overlap bounds to characterizing multiphoton indistinguishability with fewer pairwise measurements. Optimal propagation would recover the strongest bounds allowed by all the measured overlaps. The counterexample separates bounds obtained from individual triples from constraints requiring the same states to realize all measured pairs together.

## Gap

The bounded literature check recorded before any Lean in #23699 reports:

- the optimality question persists from arXiv v1 to v3;
- the orchestrator screened the titles of 40 INSPIRE citing records, with 26 citations reported by Crossref, and searched the TeX of arXiv:2605.14395, 2604.18833, 2412.09070 and 2506.17132 for discussion of the procedure's optimality, finding no settlement;
- the search contributor reported full-text checks of 22 citing arXiv works without an answer to this question;
- the preregistration's repository searches found no existing settlement.

`not-found-in-searched-scope`.

## Route

Use vertices $A,B,C,D$, corresponding to indices $0,1,2,3$, with $C,D$ the unknown pair. The five given overlaps in `givenOverlaps` are $r_{AB}=0$, $r_{AC}=r_{AD}=r_{BC}=1/2$, and $r_{BD}=0$; the array entries at $C,D$ are ignored by `realizes`.

1. **Procedure lower endpoint.** For these exact data, `lower_half_half` gives $L(1/2,1/2)=0$, including the boundary $x+y=1$, and `lower_half_zero` gives $L(1/2,0)=0$. The only common neighbours are $A,B$. The lemma `instance_lower` identifies the set defining its supremum with $\{0\}$ and proves $\ell=0$.
2. **Nonempty feasibility.** The definition `witness` takes $a=e_1$, $b=e_2$, $c=(e_1+e_2)/\sqrt2$, and $d=(e_1+e_3)/\sqrt2$ in $\mathbb C^3$. The lemma `witness_realizes` verifies all four unit norms and every required ordered overlap for this family. The lemma `feasible_nonempty` uses that realization to prove $F\ne\varnothing$.
3. **Span saturation.** For every finite dimension $n$ and unit vectors $a,b,c\in\mathbb C^n$ with $|\langle a,b\rangle|^2=0$ and $|\langle a,c\rangle|^2=|\langle b,c\rangle|^2=1/2$, the lemma `span_saturation` proves $c=\langle a,c\rangle a+\langle b,c\rangle b$. Its proof sets the right-hand side to $p$, verifies $\|p\|^2=1$ and $\operatorname{Re}\langle c,p\rangle=1$, and uses `eq_of_norm_le_re_inner_eq_norm_sq` with its hypotheses $\|c\|\le\|p\|$ and $\operatorname{Re}\langle c,p\rangle=\|p\|^2$, supplied by these identities and $\|c\|=1$.
4. **Forced overlap.** For every $n$ and every family $\psi:\mathrm{Fin}\,4\to\mathbb C^n$ satisfying `realizes 2 3 givenOverlaps ψ`, the lemma `forced_overlap` proves $|\langle\psi_2,\psi_3\rangle|^2=1/4$. Here all four vectors are unit, the five given overlaps hold, span saturation applies to $a,b,c$, and $r_{BD}=0$ makes $\langle b,d\rangle=0$. Consequently $|\langle c,d\rangle|^2=|\langle a,c\rangle|^2|\langle a,d\rangle|^2=1/4$.
5. **Endpoint contradiction.** For this instance, `feasible_singleton` proves $F=\{1/4\}$ using both the explicit realization and the forced value in every dimension. Thus `instance_infimum` proves $\inf F=1/4$ by `csInf_singleton`. The theorem `result` specializes `claim` at $m=4$, $i_0=2$, $j_0=3$ and these realizable data; its lower-endpoint equality would give $0=1/4$. No upper-endpoint evaluation is needed for this contradiction.

## Falsifier

The refutation would miss the source question if it imposed a dimension restriction, used unsquared inner products, or treated the missing pair as prescribed. The module uses squared complex-inner-product norms, quantifies feasible realizations over all finite dimensions, and excludes both orientations of precisely the unknown unordered pair. Its explicit three-dimensional realization rules out an inconsistent set of prescribed overlaps as the cause.

The source's general procedure would have to be optimal on this one-unknown-pair subcase if it were always optimal. Every other edge is given exactly, so revisiting the inferred pair uses the same two common-neighbour inputs and the same intersection. No choice of insertion order is involved. This interpretation does not specify the behavior of implementations that also add a joint feasibility test or alter the prescribed data.

## Evidence

The canonical source is `D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/PureState/OverlapIntervalPropagationRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:30e3853d150b17952006601449ce5b20fd2a2dece45a309082fce3c156aed14b`;
- `claim`: `sha256:9d0f64c7b03a7c056c1f6625d9bbc21165d95ebef9a4a9b35d40804c01434d08`.

## Triage

Tier 1 open question of a 2020 paper, preregistered in issue #23699 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every $m\ge3$, every distinct unknown pair $i_0,j_0$ and every given array $r$ with nonempty feasible set over all finite complex dimensions, the procedure's lower and upper endpoints both equal the feasible infimum and supremum.

**Computed, not formalized** (recorded in #23699): the upper endpoint of the procedure's interval for the instance; the module uses only its lower endpoint.

**Argued, not formalized.**

- *Mechanism and missing structure.* In the formal instance, the triples through $A$ and $B$ each leave the unknown overlap free at their lower endpoint. They use $r_{AC},r_{AD},r_{BC},r_{BD}$, while the additional relation $r_{AB}=0$ makes $a,b$ orthogonal. Together with unit norms and $r_{AC}=r_{BC}=1/2$, that relation exhausts the squared projection norm of $c$: `span_saturation` gives its stated expansion. With the further given conditions $r_{AD}=1/2$ and $r_{BD}=0$, `forced_overlap` fixes $r_{CD}=1/4$. The interval intersection does not impose this common realization of the two triples. Increasing the ambient dimension cannot remove the obstruction, because those lemmas quantify over every finite dimension with the stated unit-norm and overlap hypotheses.
- *A weaker conclusion survives.* Conditional on the source's three-state inequalities, every actual realization satisfies each common-neighbour interval, so it satisfies their intersection. This follows by applying the inequality to each triple within that same realization. Valid outer bounds therefore survive even when their endpoints are unattainable. For three states and two prescribed overlaps, there is only one triple; the source's tightness statement at line 131 remains the applicable restricted result. The module does not formalize these general validity or three-state tightness statements.
- *Dimension scope.* Any finite family of $m$ vectors spans a subspace of dimension at most $m$. Choosing an orthonormal basis for that span preserves every inner product and gives a realization in some finite $\mathbb C^n$. Thus an infinite ambient Hilbert space cannot supply additional overlap values for this finite family; this reduction is not separately formalized.
- *What would have to be added.* An exact procedure must enforce compatibility of the triples with the relations among their common neighbours. In this instance, retaining $r_{AB}=0$ in the joint span argument is enough to determine the unknown value. A general sufficient compatibility criterion, or a characterization of the larger graphs and data for which interval propagation is exact, remains open here.
- *Effect on the paper.* The source poses optimality as a question, rather than as a premise of its later results. The counterexample answers that question negatively in the registered sense. Section IV.B's use of valid lower bounds for unmeasured overlaps does not require endpoint optimality; those bounds can be conservative. The source's three-state bounds, classical inequalities, and three-state coherence and dimension witnesses do not acquire a contradiction from this settlement. The separate mixed-state conjecture at line 133 and the detailed behavior with several unknown edges are outside the formal claim.

## ASSUMED-UNVERIFIED

The bounded literature check in #23699 does not establish exhaustive worldwide novelty or priority. Its v1 comparison, citation counts, four-paper TeX search, 22-work full-text search and repository-search results are attributed reports and have not been independently reproduced here. The search contributor's report that arXiv:2404.16107 settles a different, mixed-state conjecture was not verified and is not used in the refutation.

The v3 source quotation and definitions were checked directly in `overlap_pra_v3.tex`, md5 `52c4a57f4ae9ae3536a2134c036dc28d`. The source-to-`claim` interpretation, the exact upper-endpoint computation, and the arguments and source-dependency assessment in “What the settlement shows” are not additional Lean theorems. General soundness of interval propagation, three-state tightness, compatibility criteria beyond this instance, and classifications for several unknown edges are not formalized by this module. No assertion of optimal bounds for arbitrary graphs or of an optimal repair is made.
