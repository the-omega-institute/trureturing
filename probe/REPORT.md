# Perrier ECA 6:4 (2026), §5 — isolated probe

FALSIFIABLE PREDICTION (before checks): for every d and all parameters the two identities hold; a single failing (d, m, a) refutes the conjecture.

Scope: preregistered issue #8627; exact rational checks, source fidelity, pinned-library search, and kernel proof probe. No other seat output is an input. Verdict is pending verification.

## Source fidelity and rational check

Source visually inspected: printed pp. 14–15 (general recurrence/formulas), p. 12 (shifted definition and proved 3×3 formulas); text inspected for the 2×2 shifted definition. The issue's p. 7 locator for that definition is off by one: it occurs on printed p. 8. This is a locator error, not a change of statement.

Clause checks: k=d+1; source coordinate j+1 maps to Fin coordinate j; source time n−1 maps to natural index n. Initial coordinate zero is 1 and successor coordinates are a_j. Both recurrence equations agree after these shifts. D has m_j at exponent d−j and terminal term −X^(d+1); P has a_j−m_j at d−j; Q has leading X^d and a_j at d−1−j. All agree with the displayed formulas. Arbitrary fields/parameters and d=0 strengthen the real/integer k≥2 instance; no source case is lost. General-k shifted R is the explicit contextual reading already disclosed in the issue, not independently restated on p. 15. The follow-on conjecture about equation (7) is excluded. No statement-fidelity defect found.

Independent exact Fraction computation: 2,867 parameter cases, d=1..8; coefficients 0..47 for both identities (275,232 coefficient equalities), zero failures. Exhaustive {-1,0,1} parameters for d≤3 plus 256 seeded rational cases per d (numerators −8..8, denominators 1..7). Per-d counts and seed are in python-result.json. Controls: all 337 d=2 cases also match the independently printed middle-coordinate formula; d=0 checked separately. Finite checks do not prove the universal claim.

## Library-first approach

Pinned Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d. LinearRecurrence provides solution uniqueness and a characteristic polynomial, but no power-series closed form. The searched PowerSeries, matrix-characteristic-polynomial, and repository scopes contain no exact Perrier theorem; this is not an exhaustive literature claim. Search commands, exit codes, and matched-line counts are in dedupe.json; the PCRE positive control uses the same word boundaries and noncapturing alternation and returns 40 hits.

First proof attempt is explicitly bind-only: translate the recurrence by existing PowerSeries coefficient/shift lemmas, take a weighted finite sum, and cancel its two boundaries using upstream Fin.sum_univ_succ and Fin.sum_univ_castSucc. All subsequent steps are sum distribution and ring normalization. This attempts to avoid the preregistered induction-on-j elimination witness entirely. If it compiles, that witness is unnecessary, and the final shape will be reported bind-only with admission_basis open-problem-resolution; no replacement escape witness is asserted.

## Kernel result

`lake env lean probe/PerrierProbe.lean` exited 0. The complete quantified conjunction compiles; all parameters and all recurrence solutions are universally quantified, including d=0. Exact axiom output:

```text
'PerrierProbe.result' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The upstream-only weighted-sum proof succeeded. It contains no induction-on-j elimination lemma and no new helper theorem. Consequently the proposed escape witness is unnecessary: proof_shape is bind-only, with the preregistered open-problem-resolution admission basis.

Exact cache receipt:

```text
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-perrier-mcf","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## Witness-bypass mutant

`lake env lean probe/PerrierNoEliminationMutant.lean` exited 0, with exactly `[propext, Classical.choice, Quot.sound]`. It proves the same universally quantified conjunction without the proposed coordinate-elimination lemma and additionally removes the local hbalance fact by inlining its ring-normalization calculation. It does not import the main probe or assume its conclusion. The proposed witness fails necessity test (iv). This is a bind-only path, not a replacement content witness, so no altered escape witness is being retrospectively preregistered.

## Elaborated dependency audit and placement

The final main file compiles with exit 0 after adding a checked-environment traversal (no mathematical declarations added). It visits 7,334 constants in the elaborated type/proof dependency closure; zero are in D5. Direct proof providers include Fin.sum_univ_succ, Fin.sum_univ_castSucc, and PowerSeries.eq_mul_inv_iff_mul_eq. Probe-owned constants are the result, its five definitions, and compiler-generated proof auxiliaries; no elimination lemma occurs. These readings establish no direct frozen dependencies; there are no GIDs or statement_ids to report. The closure audit checks presence, not the repository's whole semantic admission policy.

Proposed GID: D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions. Proposed path adds `.lean`. Target directory has exactly 4 direct files, all Lean; adding one gives 5, within the brief's ≤12 admission band. Public delivery surface: Recurrence, R, D, P, Q, and ONE result. The no-elimination mutant and diagnostic commands are probe artifacts, not additional proposed public mathematics. No D5 mutation or admission operation has occurred.

## Judgement-form report

Verdict: **propose** — the complete preregistered conjunction and its witness-bypass mutant compile without sorry or new axioms, with only propext, Classical.choice, Quot.sound. This is a probe recommendation, not a freeze, admission, review consensus, or merge.

Both public test declarations (PerrierProbe.result and the probe-only PerrierNoEliminationMutant.result) have proof_shape **bind-only**, direct frozen dependencies **none**, escape_witness **none**, and admission_basis **open-problem-resolution** (issue #8627). Only the main result is proposed for delivery.

Four witness tests, applied to the preregistered induction-on-j elimination lemma:

1. In elaborated dependency closure: **fails**. No such declaration occurs; the complete main closure was traversed.
2. Not obtainable by upstream instantiation/projection/normalization: **not established**. Actual proof intermediates come from existing finite-sum boundary decompositions and normalization of the recurrence hypotheses. No non-normalization fact is claimed.
3. Not definitionally the conclusion: the proposed general-j statement differs from the final conjunction, but no such declaration was elaborated, so no kernel definitional-inequality result is claimed.
4. Live/necessary path: **fails**. The independently compiled witness-bypass mutant proves the same conjunction. iv_mutant_compiled = true.

The observation is a successful bind-only approach, not a different escape witness. There is therefore no retrospectively relabelled content witness. The issue already preregisters open-problem-resolution if the content-witness assessment fails.

Utility kind=none: the theorem quantifies over arbitrary dimension, field, parameters, and recurrence solutions. It is not bounded enumeration, a checker, numeric reduction, or a certified finite instance. The finite Python computations are probe evidence only.

### Boundaries and reasoning discipline

The reference frame is the literal shifted recurrence and the source formulas, fixed before computation. The known-good shapes are PowerSeries coefficient shifts and Fin's two decompositions of the same finite sum. 美不美: the matrix/charpoly route is structurally elegant but its searched APIs do not discharge these formulas; coordinate induction mirrors the source but introduces an unnecessary intermediate; weighted-sum cancellation is concise and fully instantiated from upstream identities. Aesthetic preference is not evidence: compilation, dependency traversal, and exact coefficient comparisons are the verified readings.

ASSUMED-UNVERIFIED: comprehensive novelty/open status outside the inspected source and bounded pinned-library/repository search. The issue's independent literature-search claims were read, not independently reproduced. In particular its named WSU 2023 dissertation gap remains unverified. General-k use of the earlier shifted R definition is a contextual interpretation disclosed in the preregistration, not an explicit repeated definition on p.15.

Depth-bound stop: complete main conjunction plus one successful witness-bypass mutant; no further claim about equation (7), classification of periodic continued fractions, or the unread dissertation. The dependency traversal bound was 100,000 constants and it completed at 7,334. No required CI gates, deposit, emission, preflight, PR, or other-seat review was run or claimed.

Visible inputs: this brief + GoalArtifact + issue #8627 + source PDF; inherited prior: repo-prior-exposed (CLAUDE.md/AGENTS.md). Pinned Mathlib and repository sources were read for the requested search; no other probe seat output was accessed or requested.
