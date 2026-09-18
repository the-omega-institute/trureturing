# Bradshaw Conjecture 20 probe

## Preregistered falsifiable predictions

Recorded before source retrieval, searches, computation, or Lean execution.

1. An independently written Python arithmetic derivative D and generalized Collatz map C will reproduce the paper's printed initial solution lists: (a,b)=(5,3): 12419, 20171, 37727, 134579; (7,1): 429 only in the paper's stated search range; (7,5): 29831, 38051, 76331.
2. At (a,b,n)=(17,7,125), D(C(n))=C(D(n)), and 125 is not squarefree.
3. The preregistered claim agrees clause by clause with the source, with the explicitly requested restriction 1 <= n.
4. The expected proof shape is bind-only, with admission_basis open-problem-resolution. A successful Lean refutation must construct an admissible arithmetic derivative and derive its witness values from the four defining properties.

Success requires independent source fidelity, the Python anchors and witness, and a Lean proof with no sorry, no native_decide, no new axioms, and only the standard axiom closure. Source mismatch ends this attempt with revise; unfinished verification is abstain.

## Status

Predictions recorded. Checks have not run.

## Source fidelity

Independently retrieved the JIS PDF from the supplied URL (215463 bytes); third-party material remains in runner scratch. Printed page 3, Section 2, defines D : N -> N by D(0)=0, D(1)=0, prime values 1, and the product rule for every m,n. Printed page 16 gives the odd/even branches of C and the sole parameter condition a congruent to b modulo 2. Conjecture 20 asserts squarefreeness of every commuting input.

Issue #8643 matches each of these clauses. The extra hypothesis 1 <= n is explicit in the preregistration: it weakens the source claim, so its refutation implies a refutation of the source. The witness uses positive odd a=17, b=7 with b<a, so does not exploit an unstated zero-parameter convention. Quantification over admissible D implements the source characterization; the Lean proof must exhibit one to exclude vacuity. Minor locator correction: the four defining properties are on printed page 3 (not page 2).

## Independent Python result

`python3 probe/check_bradshaw.py` exited 0. The independently implemented prime-power contribution sieve reproduced all five complete printed lists over 1 <= n <= 10^7, including the sole (7,1) solution 429. A separate trial-factor formula agreed on D(0..9999). Full lists, sieve bounds, and elapsed time are retained in `python-results.json`.

At (17,7,125): D(125)=75, C(125)=1066, D(1066)=641=C(75), D(75)=55, and 125 has factorization 5^3. Both preregistered numerical predictions passed. These are computational checks, not a replacement for the Lean existence and refutation proofs.

PDF SHA-256: `5d2579130e5a88b1f3aec05d6d00d0e9876c85db42846fb05c76572a2aaed6bd`.

## Dedupe and capability result

Repository name search returned 10 lines, all in Library prose; focused Leibniz search returned 26 lines. The relevant nearby result is `D5.S3.PrimeForms.PrimaryPseudoperfectPortComposition.squarefreeDeriv_mul_of_coprime`, read in full: its sum has no valuation multiplicity, and its product rule requires coprimality. Thus it cannot implement D on 125 (its quotient sum is 25, whereas D(125)=75). No exact admissible arithmetic-derivative definition or all-input product rule was found in the searched repository scope. Repository positive control `Nat.factorization`: 301 matching lines.

After cache provisioning, pinned Mathlib db584cd6d46c92f209a44c0f1c829460d327499d returned 0 name hits and 0 number-theory/natural-number product-rule hits. Positive control `theorem factorization_mul`: 4 lines. Reuse `Nat.factorization_mul`, `Nat.Prime.factorization`, `Nat.dvd_of_mem_primeFactors`, `Nat.mul_div_assoc`, and Finsupp finite-sum identities directly inside the proof. Search commands and exact scoped counts are in `dedupe-results.json`; all shell globs were quoted (subprocess argument vectors do not expand globs).

External Lean searches returned one unrelated real-autodifferentiation file (opened and excluded), and no arithmeticDerivative/arithmetic-derivation declarations. GitHub issue search found only #8643. Independent arXiv checks: arithmetic derivative + Collatz: 0; arithmetic derivative positive control: 11; Bradshaw + Collatz: 0. HTTP 406 from initial urllib requests was resolved using curl; successful HTTP 200 results are retained. No known settlement found in this scope. Comprehensive literature novelty remains ASSUMED-UNVERIFIED; this seat did not search citation indexes, MathSciNet, zbMATH, or OEIS independently.

## Cache gate

The supplied PATH was exported verbatim. `make lean-cache-ensure` exited 0 before any lake invocation. The initial missing Mathlib checkout was a capability gap, not a negative search; the successful searches above supersede those failed attempts.

```
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-bradshaw-probe","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```
