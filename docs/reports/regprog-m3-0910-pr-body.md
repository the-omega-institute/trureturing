Register five frozen causal peers on the canonical shared arenas

Skill context: `consensus-rnd:sshx`, implementation flight `regprog-m3-0910`, attempt 1. Carrier: one codex-cli implementation seat, GPT-6, repo-prior-exposed through AGENTS.md / CLAUDE.md. Mixing: the owner supplies the approved P2 plan and vacuity contract; this seat authors the registrations and runs local checks. Three blind review seats belong to the caller's subsequent stage; no review vote or orchestrator verification is claimed here.

This content-plane change asks whether five previously observed frozen theorems can acquire faithful registrations through the landed separation template on the two existing causal arenas, and what unique capture remains in each maximal shared catalog. No freeze, cover, theory/spec edit, or judge-plane change is part of this unit.

## Preregistered selection

The selection is fixed before registration code. The source is the frozen public theorem inventory, screened with `rg -w` over canonical carrier names, `Fin 3`, and `Bool × Bool × Bool`, plus source-module importers. The [statement inventory](regprog-m3-0910-selection.jsonl) contains 167 carrier-screen hits: 157 `observed` and the 10 certified gold theorems. Every row includes the full pretty-printed statement, statement identity, carrier labels, and a family-fit assessment. All five fixed picks assess as `observed` in `InformationRoot` scope.

Canonical arena names below abbreviate the existing declarations under `D5.S3.ConceptDynamics.InformationEscapeArenas`: IC = `FourthFifthArenas.interventionArena` (16 outcome-table SCMs); OI = `ObservationIntervention.observationInterventionArena` (32 direction/root/child SCMs). These are different carrier types with the same short type name `DeterministicBoolSCM`. The canonical declarations, signatures, and state enumerations are reused verbatim.

| Pick / frozen module and theorem | Statement (source notation) | Arena | Family / reason |
| --- | --- | --- | --- |
| 1. `Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer` | `(∀ M N, CF M = CF N → Int M = Int N) ∧ ∃ M N, Int M = Int N ∧ CF M ≠ CF N` | IC | `separation`; the inclusion is the existing collapse identity, so the additional constraint is separation. |
| 2. `Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber` | `∃ μ M N, M ∈ couplingFiber allSingleWorldMarginals μ ∧ N ∈ couplingFiber allSingleWorldMarginals μ ∧ CF M ≠ CF N` | IC | `separation`; eliminate or introduce the common fiber label without changing either readout. |
| 3. `Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable` | `¬ ∃ f, CF = f ∘ allSingleWorldMarginals` | IC | `separation`; the existing factorization/fiber theorem and classical quantifier duality give exactly a separated pair. |
| 4. `Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not` | `Refines (canonicalTargetReadout interventionMarginal) interventionMarginal ∧ ¬ Refines (canonicalTargetReadout counterfactualJoint) interventionMarginal` | IC | `separation`; reuse universal sufficiency/factorization and discharge self-sufficiency by identity. |
| 5. `InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation` | `ker (fun M action => match action with none => Obs M \| some x => Int M x) ⊂ ker Obs` | OI | `separation`; the null-action coordinate supplies inclusion, and strictness is exactly an Obs-equal / Int-different pair. |

The IC catalog contains its gold `intervention_strictly_weaker_than_counterfactual` and picks 1–4 (five occurrences). The OI catalog contains its gold `observation_strictly_weaker_than_intervention` and pick 5 (two occurrences). Every occurrence uses exactly the two readouts named in its canonical law, without anchors. The two gold shadows are reconstructed with the landed template and compared to their hand bundles.

Prediction: each new bundle has the same agreement kernel as its arena's gold bundle. Therefore every occurrence has zero unique capture in its maximal shared catalog, and the unchanged maximal seal rejects with `IE-C007`. This is a preregistered negative result: catalogs remain maximal, no arena clone or singleton seal substitutes for admission, and positive-after-seal remains false if the prediction holds. The selection probe and five theorem-specific bridges must validate the premises; a bridge exceeding 30 lines is an obstruction, not permission to change the selection retrospectively.

Stop: five new registrations, four hours, or fewer than five honest fits with bridges at most 30 lines. Lean additions are bounded by 600 net lines. The deliverable ends with a pushed PR against dev, with auto-merge disabled.

## Selection evidence and limits

`rg -l -w 'FourState|PreemptionTrace|ResidueState|SpectrumAtom|DeterministicBoolSCM|Agenda|BinaryInterpretationContext|Fin 3|Bool × Bool × Bool' D5 --glob '*.lean'` supplies 137 source paths. Frozen public theorem identities from their defining modules and immediate importers supply 718 candidates in 153 modules, excluding registration infrastructure. The standalone `SelectionProbe.lean` imports those modules and `InformationRoot`, follows statement types and D5 definition bodies (never theorem proof bodies), detects the eight named carrier declarations plus `Fin 3` and the Bool triple, and calls `CensusQuery.assess` for each hit. Frozen membership is `Golden/Frozen/state/<source>.json`; statement identities come from Lean, not name matching.

Carrier-hit counts, with overlapping labels: `Fin 3` 134, IC SCM 18, OI SCM 4, Bool triple 3, ResidueState 3, PreemptionTrace 2, SpectrumAtom 2, Agenda 1, FourState 1, BinaryInterpretationContext 1. These are statement/definition screening counts, not semantic peer counts. For example, a nested Bool triple in a five-Bool history is a false carrier match, and many `Fin 3` hits use it only as a matrix index. The inventory retains these exclusions explicitly. The search is bounded to the stated module/importer window; global completeness and impossibility of alternative bridges are ASSUMED-UNVERIFIED.

The five picks preserve the complete source statement with short fiber, factorization, or kernel-strictness transport. The unselected named-carrier statements require different canonical readouts, assert inclusion without separation, or conjoin additional independent domains. Their inventory labels are statement-shape assessments, not proofs that no other honest family exists. The registration stop is exactly five new occurrences.

## Verification and result

The maximal catalogs have zero unique capture at every occurrence. The actual seal rejects IC with `IE-C007`, `full=0`, `without=0`; the same proof builder rejects the complete OI catalog with `IE-C007`, `full=24`, `without=24`. The global seal stops at IC, so OI is checked independently through `prepareProofs` with its unchanged complete catalog. Both arrays of zero indices are kernel-certified by the existing seal machinery. No finite-occurrence seal is published, and all seven occurrences assess as `observed` in the new root. This is the brief's permitted all-zero finding, not a positive maximal seal.

The per-occurrence measurement uses ordered distinct state pairs. “Before” evaluates the same theorem unit alone as a counterfactual measurement; it creates no singleton registration or seal. “After” is the full canonical catalog. Eligible means the frozen statement has a checked full-statement bridge and the vacuity witnesses; registered is registry membership; positive requires both unique capture greater than zero and LowersEscape after sealing. The last two columns are checked independently of certification by `all_peers_trivial` and `no_peer_lowers_escape`.

| Occurrence / statement | Arena | Family | Authored lines (bridge) | Unique before → after | Eligible | Registered | Positive after seal | TrivialInCatalog |
| --- | --- | --- | ---: | ---: | --- | --- | --- | --- |
| Pick 1: CF-kernel inclusion and Int/CF separation | IC | separation | 9 (5) | 240 → 0 | yes | yes | no | yes |
| Pick 2: CF varies in one marginal coupling fiber | IC | separation | 13 (9) | 240 → 0 | yes | yes | no | yes |
| Pick 3: CF has no factorization through all marginals | IC | separation | 12 (8) | 240 → 0 | yes | yes | no | yes |
| Pick 4: marginal sufficiency and counterfactual nonsufficiency | IC | separation | 16 (12) | 240 → 0 | yes | yes | no | yes |
| Pick 5: full intervention-profile kernel is strictly below Obs kernel | OI | separation | 22 (18) | 968 → 0 | yes | yes | no | yes |
| IC gold: `∃ M N, Int M = Int N ∧ CF M ≠ CF N` | IC | separation | shared overhead | 240 → 0 | yes | yes | no | yes |
| OI gold: `∃ M N, Obs M = Obs N ∧ Int M ≠ Int N` | OI | separation | shared overhead | 968 → 0 | yes | yes | no | yes |

Authored lines count each physical line from the theorem-specific bridge declaration through its registration and expected-occurrence manifest, excluding the preceding comment. The five spans total 72 lines, median 13; the largest bridge is 18 lines, below 30. The single new Lean module has 336 lines, with 264 shared lines for headers/imports, template reindexing, two gold shadows, all witnesses, catalogs, kernel counts, maximal-membership checks, expected failures, census checks, and axiom prints. Net new Lean is 336, below 600. `separation` gains five distinct frozen consumers, from two causal golds to seven; it remains the sole reused template. The eight single-consumer helpers gain no reuse, and the library requires no extension.

Vacuity evidence is shared by definitional equality of each arena's occurrence bundles: `intervention_exact_use` / `observation_exact_use` give exactly the two law readouts and empty anchor domains; unrestricted `*_gold_kernel_equal` compares the hand bundles; `*_law_sensitive` proves the actual law and refutes a constant realization at the same signature; `*_nondegenerate` and the canonical `*Enumeration` witnesses cover every state. The engine checks every measured catalog unit against its complete registry vector and checks the canonical arena type. All seven `CensusQuery.assess` calls return `observed` in this root after rejection. The two golds remain certified in their original `InformationRoot` scope; certification is root-relative.

`#print axioms` over all seven registered units, the five bridges, kernel-equality/exact-use/law-sensitivity witnesses, nondegeneracy/enumerations, and before/after conclusions has union `{propext, Classical.choice, Quot.sound}`. No `sorryAx`, `native_decide`, or new axiom enters the module. The new D5 module has a `utility: none` header and a matching Blueprint source and emitted mirror.

| Command | Exit | Evidence |
| --- | ---: | --- |
| `make lean-cache-ensure` | 0 | Warm project and dependency cache provisioned through the supported target. |
| `make lean` | 0 | Imported dependencies compile. |
| `lake env lean <attempt>/SelectionProbe.lean` | 0 | 167 statements assessed; all five selected rows are observed. |
| `lake env lean D5/S3/ConceptDynamics/InformationEscape/SharedArenaPeers.lean` | 0 | All bridges, witnesses, capture counts, expected rejections, maximal catalogs, and seven census queries pass. |
| Same root with the two expected-error guards absent | 1 | Exactly two IE-C007 errors: IC full/without 0/0 and OI full/without 24/24; no proof errors. |
| `make lean-report` | ASSUMED-UNVERIFIED | Pending producer completion. |
| `make emit` | ASSUMED-UNVERIFIED | Requires the fresh Lean report. |
| `make gate` | ASSUMED-UNVERIFIED | Pending. |

The negative finding refutes positive shared-arena admission for these five registrations with the fixed canonical readouts. Reuse reduces bridge authorship, while identical peer kernels prevent unique capture. Any change of semantic arena or readouts belongs to a separately justified change of Γ. Further registrations stop at the five-pick budget; independent blind review and global inventory completeness are ASSUMED-UNVERIFIED.

`question_answered`: the shared-arena peer registration question above, preregistered in this file.
`dominating_theorem_search`: found `RegistrationTemplates.separationLegacy`, `CounterfactualIdentifiabilityCriterion.counterfactual_identifiable_iff_constant_on_fiber`, `UniversalSufficiencyFactorization.universal_sufficiency_factorization`, and `Catalog.same_kernel_both_zero` in D5; these supply the existing mathematical APIs. `Function.factorsThrough_iff` and `Set.ssubset_iff_exists` are exact pinned-Mathlib hits. No new causal theorem is proved or claimed.
