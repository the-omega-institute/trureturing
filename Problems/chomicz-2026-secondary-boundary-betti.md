---
slug: chomicz-2026-secondary-boundary-betti
bibkey: chomicz2026minimalpresentations
doi: 10.48550/arXiv.2609.04000
url: https://arxiv.org/abs/2609.04000v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.result
---

# Secondary boundary Betti degrees

## Problem

Kazimierz Chomicz, *The type and cardinality of minimal presentations of numerical semigroups with embedding dimension four*, arXiv:2609.04000v1, Section 3.2 immediately after Lemma 3.13 (`main.tex:1050`):

> However, we do not know whether $b_{22}d_2$ and $b_{33}d_3$ are Betti elements. This gap will not affect the results of Section \ref{section_type}, so we leave it unresolved.

The [source note](../Library/Semigroups/chomicz2026minimalpresentations.md) records the primary locator and interpretation. The source asks about both boundary degrees on the whole ordered secondary domain. [Preregistration #29790](https://github.com/the-omega-institute/trureturing/issues/29790) preserves the stronger full claim and independent formalization scope. The ordinary argument is attributed to public [#28454](https://github.com/the-omega-institute/trureturing/issues/28454), producer `07b67e50-10a4-41b3-9622-660f37c654a5` and its research contributor; no rediscovery is claimed.

### Full registered assertion

For every positive, minimally generating gcd-one four-tuple, least critical and distinguished-positive coefficient data exist. For every choice of those least data giving ordered secondary data, and separately for each $i\in\{2,3\}$, put
$p=\gcd(d_0,d_1)$, $r_i=p/\gcd(p,d_i)$ and $n_i=b_{0,ii}d_i$. Then

$$n_i\in\operatorname{Betti}(S)\quad\Longleftrightarrow\quad b_{0,ii}=r_i.$$

At equality the entire fiber graph has exactly two distinct, nonempty connected components: all factorizations supported on $\{0,1\}$ and all supported on $\{2,3\}$. Otherwise the entire fiber graph is connected. The assertion imposes no generator, degree, coefficient or fiber bound and assumes no desired representation.

### Statement echo

| Source or registered clause | Lean counterpart and boundary |
| --- | --- |
| Four nonnegative factorization coordinates | `Factorization := Fin 4 → ℕ`, `eval`, full `Factorizations d n` |
| Positive minimal numerical generators | `IsNumericalGeneratingTuple`; Reg `source_semigroup`, `source_excluded_generator`, `source_set_gcd`, `source_cofinite`, `source_distinct` supply the domain bridges |
| All least coefficients exist | First conjunct of `claim`, supplied by `coefficient_data_exists`; no existence assumption hides an empty minimum |
| Every allowed least datum and relation witness | Universal `d,a,b`; `IsLeast` predicates, `IsMinimalRelation`, `IsPositiveMinimalRelation`; no unique off-diagonal witness assumption |
| Secondary and critical-pair arrangement | `¬ IsPrimary a b` and all five conjuncts of `HasSecondaryOrdering`; literal line 230 convention and Lemma 2.2 distinctness, not numerical sorting |
| Both boundary degrees | Universal `i : Fin 4` with `i=2 ∨ i=3`; `boundaryCoefficient b i = b 0 i` |
| Fixed-fiber Betti question | `factorizationGraph`, `RRelated`, `Betti`; intermediates remain in the fiber |
| Gcd iff and complete alternatives | `result : claim`, including `HasExactlyPairComponents` and whole-graph `Connected` |

The printed ambient-chain wording is not silently identified with fixed-fiber reachability. Reg `source_fiber_chains` proves the fixed-fiber chain correspondence, while `source_ambient_chain` shows why unrestricted ambient chains give a different relation. The source's minimal-presentation theorem and its fixed-degree chains support the chosen interpretation. A universal permutation/transport theorem from arbitrary unordered presentations is not supplied; the registered event already uses the source's standing ordered convention.

## Motivation

The exact component classification determines when each of the two positive boundary degrees contributes a Betti degree and which factorization classes occur. It adds a structural criterion to the source's author-stated question. This is a recent author-stated question (source year 2026) pursued through the registered research-line route, with independent audit/formalization of an attributed ordinary proof.

## Gap

The full registered proposition has a kernel proof in `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.result`, with the accepted scoped axiom closure contained in `{Classical.choice, Quot.sound, propext}`. This mathematical fact does not certify canonical freeze, final delivery, priority or source-question KPI.

The five public four-slot escape audits remain unfinished with zero `declared_validated`. [Issue #29825](https://github.com/the-omega-institute/trureturing/issues/29825) identifies the missing whole-family variation/sensitivity, actual observational dependence, source-selection and lawful-enrollment evidence. Existing compiled conditional Reg mirrors are retained; their conditional laws do not supply the missing audit evidence. An unknown continuation and CI success do not close this gap.

## Route

`positive_minimum_excludes_coordinate` subtracts a forbidden coordinate to contradict leastness. `critical_pair_positive_representation` uses the complete two-point critical fiber to force a positive two-generator representation at the gcd threshold. `secondary_boundary_bounds` proves $a_{ii}<b_{0,ii}\le r_i$. `equality_excludes_mixed` rules out mixed left/right support at equality by coefficient leastness and a critical exchange.

In `result`, a right hub has both right coordinates positive. Equality supplies a left hub with both left coordinates positive; exclusion of mixed support partitions the whole fiber into exactly the two components. Below the threshold, divisibility excludes pure-left vertices and every vertex reaches the right hub. Coefficient existence follows from positive cross-relations and well-ordering. The consumed helper `right_hub` is bind-only and receives no independent mathematical credit.

The semantic module admission basis is `escape-witness`; `utility: none`. The 22 authored theorem declarations comprise 10 content and 12 bind-only declarations, all bind-only declarations having live consumers. All five public target theorems carry content. No `open-problem-resolution` admission exemption is used, so no alternate resolution-claim route is asserted. This unbounded structural theorem is not a finite numerical utility.

### Declaration form

All direct frozen D5 prerequisite lists for these declarations are empty; pinned Mathlib supplies the reused arithmetic and graph interfaces. The following classification distinguishes mathematical content from consumed proof organization.

| Declaration | proof_shape | Live consumers | Escape content |
| --- | --- | --- | --- |
| `eval_pure` | bind-only | `critical_pair_positive_representation`, `equality_components`, `exists_positive_coefficient`, `left_exchange_bound`, `pair_degrees`, `pair_normalization`, `secondary_boundary_bounds` | none; consumed helper |
| `eval_add` | bind-only | `critical_pair_positive_representation`, `equality_components`, `left_exchange_bound`, `secondary_boundary_bounds` | none; consumed helper |
| `eval_mem` | bind-only | `equality_components` | none; consumed helper |
| `exists_positive_coefficient` | bind-only | `coefficient_data_exists` | none; consumed helper |
| `coefficient_data_exists` | bind-only | `result` | none; consumed helper |
| `positive_minimum_excludes_coordinate` | content | `equality_excludes_mixed` | Conclusion itself, escape-witness form (2): universal exclusion obtained by the smaller-admissible-coefficient construction and leastness contradiction. |
| `pair_normalization` | bind-only | `critical_pair_positive_representation` | none; consumed helper |
| `critical_pair_positive_representation` | content | `equality_components`, `left_exchange_bound`, `secondary_boundary_bounds` | Conclusion itself, form (2); the residue-to-positive-representation inference is absent from the cited upstream residue theorem. |
| `right_fiber_vanishes` | bind-only | `secondary_boundary_bounds` | none; consumed helper |
| `secondary_boundary_bounds` | content | `equality_excludes_mixed`, `right_hub`, `strict_connected` | critical_pair_positive_representation, through the upper-bound half; the lower-bound normalization alone receives no escape credit. |
| `left_exchange_bound` | content | `move_left` | critical_pair_positive_representation on the swapped pair, live in the strict exchange bound. |
| `eval_four` | bind-only | `equality_excludes_mixed`, `move_left`, `pair_components_of_hubs`, `right_hub`, `strict_connected` | none; consumed helper |
| `threshold_divides_iff` | bind-only | `equality_excludes_mixed`, `move_left`, `strict_connected` | none; consumed helper |
| `pair_degrees` | bind-only | `equality_excludes_mixed`, `move_left`, `right_hub` | none; consumed helper |
| `move_left` | content | `equality_excludes_mixed` | The live positive-representation inference inside left_exchange_bound after same-delivery inlining; the final vector identity alone is normalization. |
| `equality_excludes_mixed` | content | `equality_components` | Conclusion itself, form (2), with live positive_minimum_excludes_coordinate and the positive-representation paths in move_left/secondary_boundary_bounds. |
| `shared_reachable` | bind-only | `pair_components_of_hubs`, `strict_connected` | none; consumed helper |
| `right_hub` | bind-only | `equality_components`, `strict_connected` | none; consumed helper |
| `strict_connected` | content | `result` | The positive-representation path in secondary_boundary_bounds.2 is live; right_hub/shared_reachable alone receive no escape credit. |
| `pair_components_of_hubs` | content | `equality_components` | The newly proved walk invariant hreach and its uses in hsep/hlsupp/hrsupp. Generic ConnectedComponent quotient APIs supply representative/equality operations, not this graph-specific invariant or partition. |
| `equality_components` | content | `result` | critical_pair_positive_representation, equality_excludes_mixed and pair_components_of_hubs all remain live in the retained pair. |
| `result` | content |  | All three nominated witnesses survive: critical_pair_positive_representation -> equality_components/strict_connected; equality_excludes_mixed -> hparts -> equality_components; pair_components_of_hubs -> component supports/exhaustion and nonreachability -> result. |

## Falsifier

An exact ordered secondary tuple violating the gcd iff, either component conclusion or coefficient existence would contradict the registered claim. The compiled proof rules out such a counterexample in its formal system under the stated definitions. An ambient-chain counterexample would concern a different relation, and failure of a stronger auxiliary statement alone would not settle the literal source question. A failure of unordered permutation transport is also distinct from the already ordered event.

## Evidence

The mathematical source is `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.lean`; its canonical narrative source is the matching Blueprint Scribe. The retained mirror is `Reg/D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.lean`. The five public theorems are `positive_minimum_excludes_coordinate`, `critical_pair_positive_representation`, `secondary_boundary_bounds`, `equality_excludes_mixed` and `result` in namespace `D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti`.

Reg `source_domain_nonempty` gives an actual compiled inhabitant with $d=(145,203,74,111)$ and $a=(7,5,3,2)$. `source_fiber_left` and `source_fiber_right` prove the complete critical fibers at $1015$ and $222$; `source_ordering` includes their distinctness, and `source_numerical` proves positivity, gcd one and minimal generation. This example witnesses nonemptiness, not the universal claim or a universal permutation theorem.

The source definitions and literal pair ordering are literature-attested. The graph encoding, domain packaging and stronger classification are repository formalization/reuse of the attributed public argument. The paper does not prove the new classification. No new Lean declaration is needed for publication metadata.

## Triage

### What the result shows

| Item | Result and limit |
| --- | --- |
| Full registered ordered event | **Proved:** `D5/S3/Arith/NumericalSemigroups/SecondaryBoundaryBetti.result : claim`, including global existence, both indices, gcd iff and both entire-graph alternatives |
| Mechanism | **Proved:** leastness excludes forbidden coordinates; full critical fibers force the positive threshold representation; mixed-support exclusion controls the two component alternatives |
| Sharp transition | **Proved:** `secondary_boundary_bounds` bounds the boundary coefficient above by the threshold; `result` makes equality precisely the Betti case and every other admissible case connected |
| Scope beyond one example | **Proved:** all allowed data and unbounded generator/degree/fiber sizes are quantified; no stronger unordered transport or relaxed-hypothesis theorem is claimed |
| Effect on the paper | **Source-attested boundary:** the quoted question explicitly says its gap does not affect the later type-section results. No revision or new proof of those results is claimed |
| Ambient printed relation | **Distinct interpreted scope:** the fixed-fiber theorem does not prove equivalence with unrestricted ambient chains |
| Further generalizations | **Open:** independent removal of the critical-fiber hypotheses, universal permutation transport and other boundary questions are not delivered here |
| Audit and delivery certification | **Unfinished:** #29825 audits; canonical freeze, final review, exact-head CI, publication/merge and eventual source-question credit remain separate prerequisites |

## ASSUMED-UNVERIFIED

The preregistration reports a bounded source/ownership/Lean-supplier search; this dossier does not certify exhaustive literature coverage, worldwide openness or priority. The primary v1 source and its exact question are attested, while the ordinary argument's provenance is public issue #28454. Independent formalization does not establish independent model priors. No eventual delivery or KPI settlement is asserted by this dossier.
