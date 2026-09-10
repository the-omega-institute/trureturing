Register five frozen causal peers on the canonical shared arenas

Skill context: `consensus-rnd:sshx`, implementation flight `regprog-m3-0910`, attempt 1. Carrier: one codex-cli implementation seat, GPT-6, repo-prior-exposed through AGENTS.md / CLAUDE.md. Mixing: the owner supplies the approved P2 plan and vacuity contract; this seat authors the registrations and runs local checks. Three blind review seats belong to the caller's subsequent stage; no review vote or orchestrator verification is claimed here.

This content-plane change asks whether five previously observed frozen theorems can acquire faithful registrations through the landed separation template on the two existing causal arenas, and what unique capture remains in each maximal shared catalog. No freeze, cover, theory/spec edit, or judge-plane change is part of this unit.

## Preregistered selection

The selection is fixed before registration code. The source is the frozen public theorem inventory, screened with `rg -w` over canonical carrier names, `Fin 3`, and `Bool × Bool × Bool`, plus source-module importers. The statement and census query inventory is pending the standalone selection probe; pending checks are ASSUMED-UNVERIFIED.

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

## Verification and result

ASSUMED-UNVERIFIED: selection census, bridges, vacuity witnesses, maximal catalogs, exact counts, axiom union, Blueprint emission, and local gate. This section is replaced by measured present-tense results before PR creation.

`question_answered`: the shared-arena peer registration question above, preregistered in this file.
`dominating_theorem_search`: found `RegistrationTemplates.separationLegacy`, `CounterfactualIdentifiabilityCriterion.counterfactual_identifiable_iff_constant_on_fiber`, `UniversalSufficiencyFactorization.universal_sufficiency_factorization`, and `Catalog.same_kernel_both_zero` in D5; these supply the existing mathematical APIs. `Function.factorsThrough_iff` and `Set.ssubset_iff_exists` are exact pinned-Mathlib hits. No new causal theorem is proved or claimed.
