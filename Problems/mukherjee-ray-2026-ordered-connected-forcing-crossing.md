---
slug: mukherjee-ray-2026-ordered-connected-forcing-crossing
bibkey: mukherjeeray2026connected
doi: 10.48550/arXiv.2611.10985
url: https://arxiv.org/abs/2611.10985v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.result
---

## Problem

Sanjay Mukherjee and Papi Ray, *On the connected zero forcing polynomial of finite trees*, arXiv:2611.10985v1, Section 5, Problem 5.3, PDF page 21:

> Given two trees T₁∈𝔗ₙ,ₚ₁ and T₂∈𝔗ₙ,ₚ₂, can we always find an integer l, with 1≤l≤n, such that Z_C(T₁,i)≤Z_C(T₂,i) for 1≤i≤l and Z_C(T₁,i)≥Z_C(T₂,i) for l+1≤i≤n?

The ordered pair is fixed before choosing the cutoff. The source explicitly allows different leaf counts, with no order on those counts or global exclusion of paths. An exchange-permitted formulation is a different statement.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every n,p₁,p₂ | Natural parameters `n p q` in `claim` |
| Every two finite vertex carriers | `V W : Type` with independent `Fintype` instances |
| Trees on n vertices | `G.IsTree`, `H.IsTree` and both carrier cardinalities equal n |
| Exactly p₁,p₂ degree-one vertices | `leafCount G = p`, `leafCount H = q`, counting neighbor subtypes of cardinality one |
| Ordinary zero forcing | Imported `ZeroForcingThree.IsZeroForcing` and `Black` |
| Initially induced-connected set | `(G.induce (S : Set V)).Connected` in `connectedForcing` |
| Number of size-i subsets | `coefficient` filters all actual `Finset V` values by cardinality and the native semantic predicate |
| Integer cutoff and both closed ranges | `l : ℤ`, `1 ≤ l`, `l ≤ n`; both implications for every `i : ℤ` |
| Positive coefficient indices | `i.toNat`, equal to the positive integer index in either range |
| Complete assertion false | Literal `result : ¬ claim` |

Arbitrary n,p,q are retained. No p≥3, common-leaf, nonpath, direction-choice or bounded-catalog assumption is added. Universally quantified finite carriers allow a Fin 4 counterexample without enumerating all trees or proving a universal relabelling theorem.

## Motivation

Tier 1: an externally published named question, source year 2026. Original pre-probe registration and bounded literature findings are in [#31033](https://github.com/the-omega-institute/trureturing/issues/31033); the formal delivery carrier is [#31076](https://github.com/the-omega-institute/trureturing/issues/31076). The prior informal settlement and its original terminal are unchanged. This is formal delivery of that same mathematical question.

## Gap

The source's Section 4 already gives the path/star pair and both coefficient lists. Their low-index orientation contradicts the mandatory first block of the later literal question. No discovery of the example or coefficient data is asserted.

The original bounded screen read the original source and history, Brimkov–Davila arXiv:1604.00740v1 Section 4.1, and relevant sections of arXiv:2611.11352v1. It found no identified settlement of this directional question; complete cited-body and citing-work coverage were not obtained. These are attributed prior findings, not a worldwide priority certification.

Current repository/private-declaration searches found native forcing and fort interfaces, which are reused, and no corresponding theory volume or exact settlement. Pinned Mathlib's simple-graph directory contains no zero-forcing match. Public GitHub code search for “connected zero forcing” in Lean returned no hits; its “zero forcing” search located the unrelated formal-conjectures TxGraffiti conjecture at f50ff7be81db666fa4c3847d9aa1b72b38e2facf, with an unfinished proof. This does not supply the present result. Network source retrieval and GitHub code search succeeded.

## Route

Use the path on 0,1,2,3 and the star centered at 0 on the same carrier. The path is a Mathlib tree; center reachability and the tree edge-cardinality characterization certify the star. Endpoint singletons force along the path. All other path singletons and every star singleton have certified disjoint forts; `IsFort.not_black_of_disjoint` excludes all derivations from those initial sets. Singleton induced graphs are connected. The entire filtered singleton-subset families therefore have cardinalities two and zero. Every admissible cutoff includes index one, contradicting the required inequality.

## Falsifier

The path edges are 01,12,23 and the star edges 01,02,03. A star leaf may force the center, but the remaining two leaves form a fort. The center singleton cannot force a leaf because it has three white neighbors. In a path interior singleton, the complement is a fort; endpoints instead force every successive vertex. This certifies the source's singleton coefficients from the native semantics rather than assuming the printed coefficient table.

## Evidence

The source module is `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.lean`. Its public definitions are `connectedForcing`, `coefficient`, `leafCount` and `claim`; its only public theorem is the designated `result`. The private graph, decidability instance and singleton helpers all occur on the live result path. The designated result has the four-slot registration exemption; no other public theorem is introduced.

Proposed `proof_shape: bind-only`; `admission_basis: open-problem-resolution` under original #31033; `escape_witness: none`. The proof applies frozen forcing/fort semantics, pinned graph interfaces and finite normalization. Consumed helpers are mathematical organization, not separate mathematical novelties. Utility is `certified-instance` with `refutes` directed at the literal claim and result. Final shape and fidelity require independent prefreeze evaluation.

## Triage

The failure mechanism is the mandatory nonempty initial coefficient block: at size one the path propagates while branching in the star leaves an unenterable fort. Thus the fixed ordered universal assertion fails independently of the high-index block. Section 4's source examples and full polynomials receive their original attribution.

Reversing this particular pair permits cutoff two according to the source polynomials. A universal version permitting an initial swap, a choice of crossing direction, or a leaf-count ordering remains open here; none inherits this settlement or its admission. The established theorems and Problem 5.2 are logically unaffected. No additional theorem is asserted under the original admission.

## ASSUMED-UNVERIFIED

Worldwide priority, exhaustive correction/citation coverage and authorial intent beyond the printed direction are unverified. Independent prefreeze evaluation, canonical freeze and publication validation are separate unmet delivery obligations. A source-attributed mathematical refutation does not itself establish a merged delivery or KPI credit.
