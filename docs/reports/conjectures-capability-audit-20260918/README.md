# Conjectures.io: proof obligations and library coverage

The accepted proofs are useful benchmarks for mathematical capabilities. They
do not establish that trureturing needs to reprove Hall, first-moment existence,
additive energy, or a general asymptotic calculus. Those prerequisites already
have substantial library support. The informative obligations are the
construction-specific estimates and invariants that make the prerequisites
applicable.

## Scope and versions

This is a bounded source audit dated 2026-09-18. The D5 search and local import
probes use trureturing commit
`2636f7c8202a04cfee1eb6516754c95dded5ebad`, Lean `4.33.0`, and
[Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`][mathlib].
The inspected result records identify FormalConjectures catalog commit
`8432eac998110a563e03df65a28c117e97c8c142`.
Additional external-library searches use a different
[FormalConjectures snapshot, `dad8f20847def1241950d466768df630e74ad00d`][fc],
whose Lean version is `4.33.1` and Mathlib pin is
`0df444a360eaa60ab8c11dca51a86af692955474`.
Availability in that snapshot does not imply admissibility or compatibility
with the project's pin.

Five accepted result records were read for scope: #272 strong, #108,
#14(i), #196, and #18(b). Four published proof files (#272, #108, #14(i),
#196) were sampled at their final dependency paths and key intermediate
statements. The external proofs were not fully audited or locally replayed.
Their verification status below is the site's report, not a new certification.

At this observation, the [results page][results] reports 32 submissions:
27 Lean verified and 5 Lean rejected. Among the 27 verified table rows,
17 have approved reviews, 5 partial awards for task defects, and 5 rejected
reviews (2 prior formalizations, 2 prior solutions, 1 duplicate).
Desktop/mobile copies are not separate records. These are submission counts,
not the number of newly solved Erdős problems; the page also contains Green
problems, variants, and parts.

The site separates kernel acceptance from source/semantic review and reward
eligibility. Inspected records say the independent Nanoda kernel was not run.
#108 and #18(b) disclose separate review contexts of the same model family
and no fresh review-stage replay. The public records expose neither the
private search process nor its cost. Validator time cannot explain research
productivity. The [selection description][how] additionally favors compact
targets with a standard Mathlib surface, so this is a selected challenge set.

## Four proof paths that expose useful capabilities

| Accepted target | Source-level path used by the final result | Consequence for our work |
| --- | --- | --- |
| [#272 strong][r272]: unrestricted `maxArithInterCard(N) = N²/2 + O(N)` | `eventually_structural_reduction → structural_reduction → finite_upper_bound_of_structural_reduction → target_of_finite_upper_bound → target` in the [published source][p272]. The reduction handles every sufficiently large near-extremal admissible family, loses at most `2048 N`, and supplies either a common-point or a controlled long-interval structure. The final upper-bound constant is `30000`. | The substantive obligation is the universal structural reduction. This exact asymptotic target is excluded from new-solution selection. The record does not settle an exact extremal formula or classify every extremizer. |
| [#108][r108]: refutation at `r=5, k=7` | `model_badColor_probability_le` and `model_badSparse_probability_le`, with `model_sizes_exist`, feed `exists_avoiding_of_finiteProb_lt_one` inside `model_base_exists`; then `arc_counterexample_family → counterexample_family → target` in the [source][p108]. | This uses **probabilistic base-graph existence followed by deterministic arc-graph transport**. The hard estimates ensure both properties hold in the same realization. It is evidence for the user's combined probability/construction direction. |
| [#14(i)][r14]: exception count for unique two-term sums | `finite_obstruction → set_scale_obstruction → uniform_sqrt_bound → part_i_positive → target` in the [source][p14]. The finite proof combines representation/triple counts, prefix estimates, and generating-function bounds. It gives `sqrt(N) < 12000 E_A(N)` for `N ≥ 2·10²⁴`, then `N^(1/2-ε) =O(E_A(N))` for every `ε>0`. | The representation convention is unordered pairs including the diagonal, with exceptions in `1..N`. The strong finite obstruction carries the mathematical content; the final Big-O conversion directly uses existing analysis. Part (ii) with a shared core is not an independent consumer. |
| [#196][r196]: permutation avoiding four-term APs in both orientations | `finite_saturation`, `extend_closed`, and `extend_compatible` establish `finite_extension`; nested `stage` lists give `permFun_agrees`, injectivity, surjectivity, and AP avoidance before `counterexample → target` in the [source][p196]. | The key finite invariant must be strong enough to survive extension. Passing to a global object requires stability and eventual coverage; there is no unproved extension premise. This is distinct from finite-to-asymptotic transfer. |

#108's `model_base_exists` states, for `q≥1` and `K≥4), the existence of
a finite base graph that is not `2q`-colorable while every subgraph of maximum
degree at most `K` is 4-colorable. The arc construction turns the appropriate
four-cycle-free subgraphs into 6-colorable graphs and forces arbitrarily high
ambient chromatic number. An arc operation alone would not establish the base
graph's simultaneous properties.

#272's `target_of_finite_upper_bound` uses `IsBigO.of_bound`, attainment of
the maximum, and a lower bound to control the absolute error. An upper bound
alone would not establish the displayed two-sided Big-O error. The final proof
explicitly provides `structural_reduction`; the earlier conditional theorem
is not the final result.

#196's extension contract is:
`Good P → ∀ F : Finset ℕ, ∃ Q, Good Q ∧ P <+: Q ∧ ∀ x∈F, x∈Q`.
Here `Good` includes nodup, an AP closure condition, and a compatible binary
preference system. “Every finite object extends” without those preservation
conditions would not be the same theorem.

The [#18(b) review][r18] supplies a fifth scope check: its final factorial
bound `h(n!) < n^ε` eventually for every positive `ε` discharges the weighted
dyadic-mixing premise internally. This audit did not inspect that proof file.

## Existing library knowledge and precise limits

Classification applies to individual obligations:

* **A:** an existing frozen D5 declaration covers the exact obligation.
* **B:** an existing upstream proof covers it; use the library, subject to the
  exact version, domain, and hypotheses.
* **C:** a repeatedly needed content statement remains after the dominating
  theorem search, with two distinct live consumers.
* **U:** coverage or transfer has not been established. This is an uncertainty
  marker, not a fourth source of mathematical content.

The following are library entry points, not claims of complete coverage of
any external proof.

| Capability | Concrete source | Classification and boundary |
| --- | --- | --- |
| Ordered finite representations | [`Finset.addConvolution`][convolution], `addConvolution_ne_zero` | B. Counts ordered pairs. #14's unordered-plus-diagonal convention requires an explicit comparison. |
| Energy expansion and Cauchy–Schwarz | [`addEnergy_eq_sum_sq'`, `card_sq_le_card_mul_addEnergy`, `le_card_add_mul_addEnergy`][energy] | B. In particular `|A|²|B|² ≤ |A+B| E(A,B)` is already present. The sumset-restricted expansion works without a finite ambient group. |
| Ruzsa covering and Plünnecke–Ruzsa | [`Finset.ruzsa_covering_add`][ruzsa]; [`Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add`][pluennecke] | B. Even this larger theory is available upstream. Lack of a D5 keyword hit is no reason to reprove it. |
| Global witness injection from Hall | [finite `all_card_le_biUnion_card_iff_existsInjective'`][hallfinite]; [`all_card_le_biUnion_card_iff_exists_injective`][hall] | B. The latter handles arbitrary index types with finite neighborhoods, as used by #272's `exists_axis_matching`. Establishing its Hall premise is a separate obligation. |
| LYM and Sperner | [`local_lubell_yamamoto_meshalkin_inequality_mul`, `IsAntichain.sperner`][lym] | B. Uniform-layer sizing and antichain hypotheses matter. They are not arbitrary-family shadow bounds. |
| Compression | [`UV.card_compression`, `UV.card_shadow_compression_le`][compression] | B for the stated UV construction and hypotheses. Preservation of arithmetic-progression intersection constraints is not established by those conclusions. |
| First-moment deterministic existence | [`MeasureTheory.exists_le_integral`, `exists_integral_le`][average] | B on a probability measure, with integrability. Applying the latter to `good − λ·bad` only chooses a sample; a deletion operation must still preserve admissibility and control cost. |
| Finite product sampling | [`ProbabilityTheory.uniformOn_pi`][uniform] | B for independent coordinate sets with finite index/domain assumptions. The dependent coordinate choices and bad-event bounds in #108 still need matching to this interface. |
| Probability in D5's capture model | [`escape_bonferroni_bounds`][bonferroni]; [`capture_count_variance_and_lower_bound`][moment] | Frozen D5 results give union/Bonferroni bounds and `(E X)²/E(X²) ≤ P(X>0)` for the specific normalized listing/capture model. Cross-domain coverage of #108 is U; no identification of that model with the graph sample is claimed. |
| Finite bounds to asymptotics | [`Asymptotics.IsBigO.of_bound`][bigO] and [power asymptotics][powers] | B for standard envelope/limit operations. A new error estimate can be content; a new name for an already supplied estimate plus this constructor is bind-only. |
| Additive bases and natural density | [`Set.IsAsymptoticAddBasisOfOrder`][basis], [`Set.HasDensity`][density], and [finite averaging][finitemethod] in the external snapshot | Existing external definitions/proofs, but project import compatibility is U. `Set.HasDensity.hasLogDensity` there is `proof_wanted`, not a proved dependency. Audit declaration bodies, not just names. |
| Graph invariant transport | [`chromaticNumber_mono_of_hom`, `Colorable.of_hom`][coloring]; [`egirth_anti`, `IsContained.egirth_le`][girth] | B. Natural-valued `girth` is zero on forests; `girth_anti` requires nonacyclicity. Use extended girth for unconditional monotonicity. Operation-specific statements in #108 remain separate obligations. |

Local import/name-and-type probes checked the first eleven declarations listed
in the validation paragraph below against the project pin. Source inspection
supports the other entry points; it does not by itself certify an external
proof's axiom closure or its transfer into D5.

The D5 keyword search found no `HasDensity` or
`IsAsymptoticAddBasisOfOrder` occurrence in D5/Library at the audit commit.
It did find chromatic-number use in
[`DefectRelationMinimumColoring`][d5coloring], so “D5 has no graph interface”
would be false. The [finite Nathanson refutation][nathanson] concerns finite
h-fold sumsets, not the full asymptotic-basis framework. None of these text
searches proves the absence of semantically equivalent statements.

## What this means for our previous #272 work

Our [contained-pair report](../erdos272-contained-pairs/README.md) proves an
injection for a centered family with an external AP-intersection witness,
and two precisely restricted slack exclusions. These are written proofs
with a finite verifier, not frozen D5 Lean coverage.

The exceptional five-term AP case proves Hall by lower-bounding each member's
incidences and upper-bounding each hole's multiplicity. The full matching
argument also prevents collisions across the size classes and private pairs.
The remaining obligation is global: Theorem J does not control all center
choices or all outsiders. The accepted #272 source instead closes a universal
near-extremal structural reduction before using its counting bounds.
No exact equivalence between our local theorem and a published source lemma
was proved in this audit, and no new priority claim follows.

An external accepted proof is a source to reuse. Extracting or renaming one of
its lemmas does not count as a new proof of an open problem. In particular,
`partial_matching_card_le` in that source is injection plus partition
counting; its useful name is not evidence of new admissible D5 content.
Likewise, summing a supplied representation cap to obtain
`|A||B| ≤ K|A+B|` is bind-only under the project's rule.

## Priorities supported by this sample

1. **Dependency discovery first.** Record the available entry points above.
   #272 and #14 both use standard Big-O machinery at the end; this repeated
   need points first to library knowledge, not a new generic theorem.
2. **Random construction plus invariant transport.** #108 offers one
   concrete benchmark combining both. Trace the simultaneous bad-event
   estimates, the parameter choice, the sparse-cut consequence, and the arc
   transport. Do not stop at a union-bound wrapper or assume a Paley–Zygmund
   statement solves the model-specific estimate.
3. **Witness/slack conditions that imply a usable matching.** Compare #272's
   structural predicates with actual set-system and graph-neighborhood
   consumers. A generalization must provide a new premise-producing fact;
   Hall applied to an assumed Hall condition does not qualify.
4. **Finite representations and truncation.** #14 identifies real demand for
   ordered/unordered conventions, prefix control, and generating-function
   estimates. Check the external libraries before proposing new energy or
   density declarations. Our exact finite arithmetic becomes relevant when
   these hypotheses and quantifiers actually match.
5. **Finite extension to an infinite object.** #196 suggests a sixth family
   beyond the user's five. The useful work is the preservation/extension
   theorem; merely packaging an assumed chain into a limit may be routine.
   A second independent consumer is still needed for a shared abstraction.

This sample does not establish a repeated missing content theorem qualifying
for class C. Nor does it justify a numerical ranking of the five research
areas by expected solution rate. It establishes concrete questions to test:
which structural hypotheses can D5 supply, and what is the smallest remaining
statement after existing dependencies are used?

## Measurement and target selection

The benchmark unit should retain: exact target and source version; a live
proof obligation with domain and quantifiers; matching D5/upstream declarations;
unmet hypotheses; and the evidence level (source, import/type check, or full
consumer replay). Count distinct problems separately from parts with shared
proofs. A single uncovered structural obligation can block a proof even if
most of its declarations are available.

Current bounded results:

* Five accepted target scopes inspected; four proof paths sampled.
* Eleven pinned Mathlib declaration types checked locally: energy expansion
  and sumset-energy inequality; finite Hall; local LYM; Sperner; chromatic
  homomorphism monotonicity; extended and natural girth monotonicity; both
  first-moment existence directions; and `IsBigO.of_bound`.
* No full external proof replay or exact end-to-end transfer into D5 completed.
* Zero class-C generalizations established with two independent consumers.
* **New complete Erdős solutions: 0.**

Before selecting a new solution target, check the canonical page, ordinary
discussion, dedicated claims, public formalizations, and these accepted
records. A zero claim-tab count or an OPEN badge is insufficient:
[#326][e326] and [#881][e881] have ordinary-discussion answer claims, while
#108 has the accepted refutation above. [#845][e845] is already disproved.
These are exclusions, not endorsements of every claimed proof.

[#734][e734] has a conditional finite-field discussion with thirteen stated
failure modes; absence of a full claim there does not establish tractability.
The [#156 completion result][issue156] leaves the simultaneous height-covering
obligation unresolved and reports no complete solution. Neither an auxiliary
bound nor this benchmark increments the solution KPI. No new target is
selected merely because its terminology matches a library module.

[results]: https://conjectures.io/results
[how]: https://conjectures.io/how-it-works
[r272]: https://conjectures.io/results/c3277f4a-d573-42a9-bfca-e45fb2cb39ff
[p272]: https://conjectures.io/results/c3277f4a-d573-42a9-bfca-e45fb2cb39ff/solution
[r108]: https://conjectures.io/results/8c083793-9c3c-4960-8a23-869e54fcb584
[p108]: https://conjectures.io/results/8c083793-9c3c-4960-8a23-869e54fcb584/solution
[r14]: https://conjectures.io/results/dce3d778-6f52-4c27-8da0-c82d2f391b64
[p14]: https://conjectures.io/results/dce3d778-6f52-4c27-8da0-c82d2f391b64/solution
[r196]: https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73
[p196]: https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73/solution
[r18]: https://conjectures.io/results/e93a2766-4c70-4564-b565-d0c556f35929
[mathlib]: https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d
[fc]: https://github.com/google-deepmind/formal-conjectures/tree/dad8f20847def1241950d466768df630e74ad00d
[convolution]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Additive/Convolution.lean
[energy]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Additive/Energy.lean
[ruzsa]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Additive/RuzsaCovering.lean
[pluennecke]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean
[hallfinite]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Finite.lean
[hall]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Basic.lean
[lym]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/SetFamily/LYM.lean
[compression]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/SetFamily/Compression/UV.lean
[average]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Average.lean
[uniform]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/UniformOn.lean
[bonferroni]: https://github.com/the-omega-institute/trureturing/blob/2636f7c8202a04cfee1eb6516754c95dded5ebad/D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni.lean
[moment]: https://github.com/the-omega-institute/trureturing/blob/2636f7c8202a04cfee1eb6516754c95dded5ebad/D5/S0/Diagonal/Probability/CaptureSecondMoment.lean
[bigO]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Asymptotics/Defs.lean
[powers]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean
[basis]: https://github.com/google-deepmind/formal-conjectures/blob/dad8f20847def1241950d466768df630e74ad00d/FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean
[density]: https://github.com/google-deepmind/formal-conjectures/blob/dad8f20847def1241950d466768df630e74ad00d/FormalConjecturesForMathlib/Data/Set/Density.lean
[finitemethod]: https://github.com/google-deepmind/formal-conjectures/blob/dad8f20847def1241950d466768df630e74ad00d/FormalConjecturesForMathlib/Probability/FiniteMethod.lean
[coloring]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean
[girth]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/SimpleGraph/Girth.lean
[d5coloring]: https://github.com/the-omega-institute/trureturing/blob/2636f7c8202a04cfee1eb6516754c95dded5ebad/D5/S3/ConceptDynamics/GraphColoring/DefectRelationMinimumColoring.lean
[nathanson]: https://github.com/the-omega-institute/trureturing/blob/2636f7c8202a04cfee1eb6516754c95dded5ebad/D5/S3/Arith/NathansonAdditiveHBasisRefutation.lean
[e326]: https://www.erdosproblems.com/forum/thread/326
[e881]: https://www.erdosproblems.com/forum/thread/881
[e845]: https://www.erdosproblems.com/845
[e734]: https://www.erdosproblems.com/forum/thread/734
[issue156]: https://github.com/the-omega-institute/trureturing/issues/8450#issuecomment-5726927865
