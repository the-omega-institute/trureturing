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

Tier 1: an externally published named question, source year 2026. Original pre-probe registration and bounded literature findings are in [#31033](https://github.com/the-omega-institute/trureturing/issues/31033); the formal delivery carrier is [#31076](https://github.com/the-omega-institute/trureturing/issues/31076). The formal result concerns that same mathematical question.

## Gap

The source's Section 4 already gives the path/star pair and both coefficient lists. Their low-index orientation contradicts the mandatory first block of the later literal question. No discovery of the example or coefficient data is asserted.

The original bounded screen read the original source and history, Brimkov–Davila arXiv:1604.00740v1 Section 4.1, and relevant sections of arXiv:2611.11352v1. It found no identified settlement of this directional question; complete cited-body and citing-work coverage were not obtained. These are attributed prior findings, not a worldwide priority certification.

Current repository/private-declaration searches found native forcing and fort interfaces, which are reused, and no corresponding theory volume or exact settlement. Pinned Mathlib's simple-graph directory contains no zero-forcing match. Public GitHub code search for “connected zero forcing” in Lean returned no hits; its “zero forcing” search located the unrelated formal-conjectures TxGraffiti conjecture at f50ff7be81db666fa4c3847d9aa1b72b38e2facf, with an unfinished proof. This does not supply the present result. Network source retrieval and GitHub code search succeeded.

## Route

Use the path on 0,1,2,3 and the star centered at 0 on the same carrier. The path is a Mathlib tree; center reachability and the tree edge-cardinality characterization certify the star. Endpoint singletons force along the path. All other path singletons and every star singleton have certified disjoint forts; `IsFort.not_black_of_disjoint` excludes all derivations from those initial sets. Singleton induced graphs are connected. The entire filtered singleton-subset families therefore have cardinalities two and zero. Every admissible cutoff includes index one, contradicting the required inequality.

## Falsifier

The path edges are 01,12,23 and the star edges 01,02,03. A star leaf may force the center, but the remaining two leaves form a fort. The center singleton cannot force a leaf because it has three white neighbors. In a path interior singleton, the complement is a fort; endpoints instead force every successive vertex. This certifies the source's singleton coefficients from the native semantics rather than assuming the printed coefficient table.

## Evidence

The source module is `D5/S3/Combinatorics/Graph/ZeroForcing/ConnectedForcingCrossingRefutation.lean`. Its public definitions are `connectedForcing`, `coefficient`, `leafCount` and `claim`; its only public theorem is the designated `result`. The private graph and decidability instance supply the star semantics. `singleton_connected` is consumed by `result`; `path_singleton` is consumed by `result`; `star_singleton` is consumed by `result`. Each helper has `proof_shape: bind-only`: respectively singleton subtype normalization, explicit forcing constructors plus a finite fort certificate, and finite fort certificates applied to the frozen obstruction theorem. All are on the live result path. The designated result has the four-slot registration exemption; no other public theorem is introduced.

Direct frozen prerequisite owners are `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree` (`Black`, its constructors, `IsZeroForcing`, `IsFort.not_black_of_disjoint`) and `ZeroForcingThreeFinite` (`IsFort`, `finiteNeighbors`). Their exact frozen module statement identities are: ZeroForcingThree `sha256:09006a0e8fc30987321439153310f86ebfc30d7e8836789450cd5f5b90fd43eb`.

`ZeroForcingThreeFinite` frozen module statement identity: `sha256:a7fe629eed58fabb6b939cb273119655c222535b6ea86445fafe78844162c652`.

The directly reused frozen declaration identities are:

| GID | statement_id |
| --- | --- |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.IsZeroForcing` | `sha256:2301cd27898a1f6d0b2b3dde2dcc82eaf457fb6d466a7fa0b147e67131ae019d` |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black` | `sha256:ecee7cbbb43fe2c4c06476fc1102beb6fd899e4c3959e8f1490c5cf905b2ca4b` |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black.init` | `sha256:02ad18ba859203092b97a8191a102f7788ab1e670ca91d2849907f13efbbc30f` |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.Black.force` | `sha256:50cb812c98528a35ea822161c3f5c2f78b08b5680bbf3d90dd7a159a6590a50b` |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.IsFort.not_black_of_disjoint` | `sha256:3b32dc19fc1d586de89c4bb8195e7f8c61e20b3a9f9bbd2bc70bb13d9f946cac` |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.finiteNeighbors` | `sha256:dddfcb2b611b105d1d695634299bd315e73b2474282c8ebfe392e7cf12984095` |
| `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.IsFort` | `sha256:55e63ea9b332b19c719a80ddca5cbaf1b54c2c0d6deabe8d7f8853e8b97f0be8` |

Current scoped extraction confirms the literal closed negation, no registration errors, and the result axiom closure `Classical.choice`, `Quot.sound`, `propext`; no sorry or native-decide axiom occurs. The generated mathematical mirror contains all four definitions and the negative result.

`proof_shape: bind-only`; `admission_basis: open-problem-resolution` under original #31033; `escape_witness: none`. The proof applies frozen forcing/fort semantics, pinned graph interfaces and finite normalization. Consumed helpers are mathematical organization, not separate mathematical novelties. Utility is `certified-instance` with `refutes` directed at the literal claim and result. Independent prefreeze evaluation approved this proof shape and the five public statement mirrors. The module is canonically frozen with statement identity `sha256:144248de44a90450c0bfa1c2e816fbfe97c5099ab07f6c74e4ed4af3d7d1a140`. The claim declaration identity is `sha256:e7895558b299a8613db938f076c4c3d5c4968bd9b0df798e1febb64b6f829a34`; the negative result identity is `sha256:cfca8f2f0ccd014562fe43e3c0bad5d743ba743bd15d600ebbe2e96148ab5c50`.

## Triage

The failure mechanism is the mandatory nonempty initial coefficient block: at size one the path propagates while branching in the star leaves an unenterable fort. Thus the fixed ordered universal assertion fails independently of the high-index block. Section 4's source examples and full polynomials receive their original attribution.

Reversing this particular pair permits cutoff two according to the source polynomials. A universal version permitting an initial swap, a choice of crossing direction, or a leaf-count ordering remains open here; none inherits this settlement or its admission. The established theorems and Problem 5.2 are logically unaffected. No additional theorem is asserted under the original admission.

## ASSUMED-UNVERIFIED

Worldwide priority, exhaustive correction/citation coverage and authorial intent beyond the printed direction are unverified. Exact-head required CI, independent final reviews, merge and containing dev-push verification remain separate delivery obligations. A source-attributed mathematical refutation does not itself establish a merged delivery or KPI credit.
