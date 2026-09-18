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
