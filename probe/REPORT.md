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

## Lean verification

`probe/BradshawProbe.lean` compiles under the cache-stamped pinned environment. Command (after exporting the required PATH): `/usr/bin/time -l lake env lean probe/BradshawProbe.lean`; exit 0. Wall time 2.56 seconds; maximum resident set size 1646854144 bytes = 1.646854144 GB (decimal). This covers the probe module and cached imports only.

```
'result' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No sorry, native_decide, or new axioms occur in the source. The first draft failed elaboration on division normalization and the opaque squarefree decision instance; the final source uses explicit division rewrites and `Nat.squarefree_iff_prime_squarefree` with 5*5 dividing 125. Only the exit-0 run above supports the proof claim.

The local D0 is `fun n => n.factorization.sum (fun p k => k * (n / p))`. Zero and one reduce via their empty factorizations; primes reduce through `Nat.Prime.factorization`; the nonzero product law follows from `Nat.factorization_mul`, sum distribution, and exact division on prime support. Zero inputs are handled separately. The statement is therefore non-vacuous.

A local universally quantified fact derives D(125)=75, D(1066)=641, and D(75)=55 from the product axiom and prime values alone. The first two establish the commutation counterexample for any admissible D; D(75)=55 is an additionally checked consistency value, not needed to contradict squarefreeness. No witness value unfolds D0.

## Judgement form for result

- theorem: `result`
- proof_shape: `bind-only`
- direct frozen dependencies: none (only pinned Mathlib imports; no project D5 imports).
- escape_witness: null.
- admission_basis: `open-problem-resolution`, preregistration #8643.

The concrete D0 existence argument is normalization of `Nat.factorization_mul` together with existing prime, support, division, and finite-sum identities. It is essential to establish non-vacuity but is not an escape witness. Source length, a new local function, and construction of an inhabitant do not change the §3.2 classification.

Four tests on the tempting candidate “D0 satisfies the four axioms”:

(i) The construction is a local proof term within `result`, and its Mathlib dependencies occur in that proof; there is no separately declared candidate witness constant.
(ii) FAIL: the stated fact follows by the existing factorization identities, instantiation, distribution, and arithmetic normalization. No new non-binding mathematical fact is needed.
(iii) Its proposition is distinct from `¬ claim`, rather than an alias or restatement; this alone does not satisfy the conjunctive witness criterion.
(iv) The inhabitation proof is live: it supplies the admissibility premise when specializing the universally quantified claim. It is obtainable by bind-only operations, so live use does not make it an escape witness. `iv_mutant_compiled`: not run / not applicable to an escape claim (none is made). The unused third derivative value is explicitly not nominated as a witness.

The only public theorem is the externally named problem's refutation. All supporting facts and D0 are local to its proof; no public or private companion theorem is introduced.
