# Conjectures.io: proof obligations and library coverage

The accepted proofs are useful benchmarks for mathematical capabilities. They
do not establish that trureturing needs to reprove Hall, first-moment existence,
additive energy, or a general asymptotic calculus. Those prerequisites already
have substantial library support. The informative obligations are the
construction-specific estimates and invariants that make the prerequisites
applicable.

## Scope and versions

The original bounded source audit is dated 2026-09-18. Its D5 search and local
import probes use trureturing commit
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

The [19 September extension][extension], following PRs #8606/#8608 and the
[density/Sidon correction][correction], uses the separate trureturing snapshot
`1a467bbc6e27672f424674bcebbda8d51a204538` with the same project Lean/Mathlib
pins. The original four source paths (#272 strong, #108, #14(i), #196) plus
#18(b) and #653 give six accepted proof paths sampled in total. The two new
files were read along relevant final dependency paths, not exhaustively
audited. No full external proof replay or new certification was performed;
the submissions' builds use their own pinned environments. Prior source and
import/type checks remain evidence at their original snapshot, not current
full verification.

The original 18 September observation counted 32 submissions (27 Lean
verified, 5 rejected). The extended observation on 19 September 2026
(Singapore), reported in the [published extension][extension], counted
33 submissions: 28 kernel verified and 5 rejected. Among the 28 unique
verified rows: 17 approved, 5 partial awards, 5 review rejections, and 1 pending
([#859][r859], excluded from the accepted-proof benchmark). Desktop/mobile
copies are not separate records. The approved Erdős subset has 12 scopes
across 11 problem numbers, not 11 new solutions; the page also includes Green
problems, variants, and parts. The [approved #10 review][r10] explicitly uses
the pre-existing Crocker covering-congruence construction; eligibility
reflected its absence from the pinned Lean environment, not new mathematics.

The site separates kernel acceptance from source/semantic review and reward
eligibility. Inspected records say the independent Nanoda kernel was not run.
#108 and #18(b) disclose separate review contexts of the same model family
and no fresh review-stage replay. The public records expose neither the
private search process nor its cost. Validator time cannot explain research
productivity. The [selection description][how] additionally favors compact
targets with a standard Mathlib surface, so this is a selected challenge set.

## Six sampled proof paths

| Accepted target | Source-level path used by the final result | Consequence for our work |
| --- | --- | --- |
| [#272 strong][r272]: unrestricted `maxArithInterCard(N) = N²/2 + O(N)` | `eventually_structural_reduction → structural_reduction → finite_upper_bound_of_structural_reduction → target_of_finite_upper_bound → target` in the [published source][p272]. The reduction handles every sufficiently large near-extremal admissible family, loses at most `2048 N`, and supplies either a common-point or a controlled long-interval structure. The final upper-bound constant is `30000`. | The substantive obligation is the universal structural reduction. This exact asymptotic target is excluded from new-solution selection. The record does not settle an exact extremal formula or classify every extremizer. |
| [#108][r108]: refutation at `r=5, k=7` | `model_badColor_probability_le` and `model_badSparse_probability_le`, with `model_sizes_exist`, feed `exists_avoiding_of_finiteProb_lt_one` inside `model_base_exists`; then `arc_counterexample_family → counterexample_family → target` in the [source][p108]. | This uses **probabilistic base-graph existence followed by deterministic arc-graph transport**. The hard estimates ensure both properties hold in the same realization. It is evidence for the user's combined probability/construction direction. |
| [#14(i)][r14]: exception count for unique two-term sums | `finite_obstruction → set_scale_obstruction → uniform_sqrt_bound → part_i_positive → target` in the [source][p14]. The finite proof combines representation/triple counts, prefix estimates, and generating-function bounds. It gives `sqrt(N) < 12000 E_A(N)` for `N ≥ 2·10²⁴`, then `N^(1/2-ε) =O(E_A(N))` for every `ε>0`. | The representation convention is unordered pairs including the diagonal, with exceptions in `1..N`. The strong finite obstruction carries the mathematical content; the final Big-O conversion directly uses existing analysis. Part (ii) with a shared core is not an independent consumer. |
| [#196][r196]: permutation avoiding four-term APs in both orientations | `finite_saturation`, `extend_closed`, and `extend_compatible` establish `finite_extension`; nested `stage` lists give `permFun_agrees`, injectivity, surjectivity, and AP avoidance before `counterexample → target` in the [source][p196]. | The key finite invariant must be strong enough to survive extension. Passing to a global object requires stability and eventual coverage; there is no unproved extension premise. This is distinct from finite-to-asymptotic transfer. |
| [#18(b)][r18]: eventually `h(n!) < n^ε` for every `ε > 0` | In the [source][p18], `exists_dyadic_average_mixed_energy_decay` controls mixed additive energy for sets in `ZMod (2^J)` and unit dilates under residue-fiber nonconcentration at every relevant scale; `exists_dyadic_probability_flattening_iteration` chooses steps independently of `J`. `exists_dyadic_unit_product_fourier_decay` gives exponential decay, then `weighted_dyadic_mixing → target` supplies the final premise internally. | Energy, Plünnecke–Ruzsa and DFT interfaces do not by themselves supply the multiscale hypotheses or quantified saving. Exact reference-library coverage is unestablished, not proven absent. This scope does not settle the stronger polylogarithmic factorial question or all of #18. |
| [#653][r653]: asymptotically almost all pins have different pinned-distance counts | In the [source][p653], `FineSelection.exists_selection` converts normalized coarse error `r(L) → 0` into bounded row/unary corrections and injective scores on `S`, with `|S| ≥ (1−δ)|good|L² − loss(L)L²` and `loss(L) → 0`. `PhysicalAssembly.exists_realization → exists_configuration` realizes adjusted scores plus one common constant with controlled point overhead. Padding preserves distinctions at every larger cardinality; `FinalConstruction.squareFamilies` supplies the finite construction before the all-n/little-o conclusion. | Averaging and injective-image counting apply after the cost and geometric preservation facts; they do not construct them. The final proof supplies these premises. The statistic counts different pinned-distance counts, not the total number of distances. Exact reference-library domination remains unestablished. |

#108's `model_base_exists` states, for `q >= 1` and `K >= 4`, the existence of
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

#653's realization retains all original pins. Padding places a new point
beyond all old distances, increasing every old pinned-distance count equally.
Common-shift preservation and the added-point budget are essential to the
final cardinality/loss transfer, not consequences of a generic transport name.
Both new external proofs are existing reuse sources, not our new content.

## Existing library knowledge and precise limits

Classification applies to individual obligations:

* **A:** an exact frozen D5 declaration covers the obligation with its
  hypotheses discharged.
* **B:** an exact independent upstream proof supplies it, subject to the
  recorded version, domain, hypotheses, and import boundary.
* **C:** shared missing non-bind-only content survives library-first
  domination search (D5, pinned Mathlib, admissible external Lean), with two
  independent live consumers.
* **U:** coverage or transfer has not been established. This is an uncertainty
  marker, not a fourth source of mathematical content.

Freeze the reference DAG/upstream corpus for each comparison. The benchmark
solution cannot tautologically establish prior coverage of its own obligation;
after inspection it can become a reuse source without new mathematical credit.

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
| Density in D5 | Frozen [`AsymptoticDensity`][d5density]: `upperDensity`, `lowerDensity`, `HasDensity`, `upperDensity_union_le` | A for the stated natural-number density interface and union subadditivity. Counting uses `Finset.range n`; `HasDensity A d` is lower/upper equality at `d` via liminf/limsup, whereas external `Set.HasDensity` uses Tendsto. Exact transfer needs a predicate bridge, not a keyword match. |
| Sidon counting in D5 | Frozen [`SidonSet`][d5sidon]: `IsSidon`, `card_mul_card_sub_one_le` | A for `A : Finset ℕ`, `A ⊆ Icc 1 N`, and unique pair sums up to exchange, including the diagonal: `|A|(|A|−1) ≤ 2(N−1)`. This is not an unrestricted representation, basis, or energy-flattening theorem. |
| Eventual-cycle averaging in D5 | Frozen [`EventualCycleAverage.eventual_cycle_average`][d5cycle] | A for a real-valued observable on an orbit with a supplied entry time, positive finite period and exact cycle identity for every subsequent step. The horizon average tends to the uniform cycle average; eventual finite periodicity is a premise, not a general averaging principle. |
| Graph invariant transport | [`chromaticNumber_mono_of_hom`, `Colorable.of_hom`][coloring]; [`egirth_anti`, `IsContained.egirth_le`][girth] | B. Natural-valued `girth` is zero on forests; `girth_anti` requires nonacyclicity. Use extended girth for unconditional monotonicity. Operation-specific statements in #108 remain separate obligations. |

Prior local import/name-and-type probes covered the scope listed below against
the original project pin. Source inspection supports the other entry points;
it does not certify an external proof's axiom closure or its transfer into D5.

The early density keyword miss is superseded by the [published correction][correction]
and the three frozen interfaces above, linked at the immutable extension SHA.
Semantic absence never followed from that search. D5 also has chromatic-number
use in [`DefectRelationMinimumColoring`][d5coloring]. The
[finite Nathanson refutation][nathanson] concerns finite h-fold sumsets, not
the full asymptotic-basis framework. None of these interfaces automatically
supplies #18(b)'s dyadic flattening or #653's selection/geometry premises.

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

#18(b) adds a concrete multiscale estimate benchmark; #653 adds vanishing-loss
selection and geometric score preservation with a size budget. #653 and #108
do not establish one shared missing theorem: the latter needs simultaneous
graph bad-event bounds and arc-specific transport. Assuming those distinct
preservation facts and repackaging their consequences would be bind-only.

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

* Six accepted source paths sampled: #272 strong, #108, #14(i), #196,
  #18(b), #653; no exhaustive proof audit.
* Prior pinned Mathlib import/type checks covered energy expansion and
  sumset-energy inequality; finite Hall; local LYM; Sperner; chromatic
  homomorphism monotonicity; extended and natural girth monotonicity; both
  first-moment existence directions; and `IsBigO.of_bound`. This retains the
  supported listed scope, without asserting an expanded aggregate count.
* Zero full external-proof transfers into D5; no fresh Lean probe, replay,
  build, or new Lean code in this documentation synchronization.
* Zero established class-C additions with two independent live consumers.
* **New complete Erdős solutions: 0.**

For source identification, the extension records parsed-source SHA-256
`4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088`
for #18(b) and
`24c90fcc776a1bc5d3ce86fc30a2cf232c64c2c3a42f8f7c36f4b5795f0e3476`
for #653. Source availability, type compatibility, kernel acceptance,
semantic approval, prior-solution status and the complete-new-solution KPI
remain separate. The broader solution goal remains active.

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
[p18]: https://conjectures.io/results/e93a2766-4c70-4564-b565-d0c556f35929/solution
[r653]: https://conjectures.io/results/257ce6dd-e3e5-4169-9d7e-2811092977ca
[p653]: https://conjectures.io/results/257ce6dd-e3e5-4169-9d7e-2811092977ca/solution
[r859]: https://conjectures.io/results/e060355f-a728-4b06-af11-6302b5780d19
[r10]: https://conjectures.io/results/244ff2d0-399d-4e37-a307-4ff6f3cb3493
[extension]: https://github.com/the-omega-institute/trureturing/issues/8450#issuecomment-5736408741
[correction]: https://github.com/the-omega-institute/trureturing/issues/8450#issuecomment-5730875809
[d5density]: https://github.com/the-omega-institute/trureturing/blob/1a467bbc6e27672f424674bcebbda8d51a204538/D5/S3/Arith/Density/AsymptoticDensity.lean
[d5sidon]: https://github.com/the-omega-institute/trureturing/blob/1a467bbc6e27672f424674bcebbda8d51a204538/D5/S3/Arith/Additive/SidonSet.lean
[d5cycle]: https://github.com/the-omega-institute/trureturing/blob/1a467bbc6e27672f424674bcebbda8d51a204538/D5/S3/ObserverMemory/Prediction/EventualCycleAverage.lean
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
