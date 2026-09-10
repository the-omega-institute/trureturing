# A372018 odd coefficient identity — implementation record

Current implementation result: **成** under the user's stated criterion (unbounded proof, `make lean` EXIT=0, no sorry/private axioms, PR opened). PR: https://github.com/the-omega-institute/trureturing/pull/6733. The theorem is frozen without an atom. Merge and independent review are not claimed. The sections below preserve chronological checkpoints, including earlier pending states and repaired failures.

## Origin and scope

- Skill: `lean4`; implementation by the Codex worker in the supplied worktree. No independent review has been performed by this worker.
- User's orchestration context: consensus-rnd/sshx, implementation attempt 1. The user's exact rational checks for n=0..58 are reported by the user, not rerun or claimed as a proof here.
- Base: `d59adb46d4703e7fdc7ef7569c5c0919247cc87a`; branch `lane/math/a372018`.
- Tier 1. The missing argument in `A371364()` is approved as `A371364(n)` by the user.
- Target: independently defined rational formal power series satisfying the two supplied algebraic equations, and `[x^(2n+1)] A = 2 [t^n] B` for all n.
- No theory volume or atom will be created. The canonical `deposit-uncovered`/`ledger-align --add` route will be used if the proof succeeds.

## Preregistered proof route

Use u=A(x), v=-A(-x), s=u+v. Subtract the two cubic root equations and cancel u-v using its nonzero constant coefficient 2. Eliminate the product uv polynomially, without constructing Laurent series. The proposed live intermediate witness is the eliminated equation for the odd part, equivalent after removing powers of x and the factor 4 to C(1-4tC)^2=1-3tC. Identify C with the independently defined B by uniqueness. The elimination and uniqueness bridge are not yet verified.

Stop as blocked with a concrete Lean goal/error if root comparison requires false invertibility or the uniqueness bridge cannot be completed. No finite check will be described as progress on the unbounded theorem.

## Search receipts

- Read all of `CLAUDE.md` in chunks after the initial full-file tool output was truncated; read `agents/CONTEXT.md` and the Lean skill.
- D5 preliminary search: `rg -n 'A372018|A371364|PowerSeries|power.series|convolution_pairing' D5 --glob '*.lean'` found many power-series modules; output was too broad and was truncated. This is a discovery pass only, not a completed public-API audit. Targeted follow-up is pending.
- Pin files read: Lean 4.33.0; lakefile mathlib tag v4.33.0. Manifest commit verification pending.
- Spec A5.1 read: general mathematical results use the exact header `utility: none` when all declarations fall outside the four computational classes.
- External source pages: ASSUMED-UNVERIFIED until individually opened below.

## Declaration accounting

No public declarations or frozen dependencies yet. `proof_shape`, `escape_witness`, direct frozen GID/statement_id pairs, and `admission_basis` will be recorded per declaration as implemented.

## Validation

Not run yet. Required order: `make lean`, `make lean-report`, `make emit`, Scribe content checks, freeze, commit, push. No `native_decide`, no cold bare Lake, no `make preflight`.

## Not claimed

No formal proof, counterexample, literature novelty, independent review, successful build, freeze, or PR is claimed at this checkpoint. The user supplied Vieta sketch remains unverified here.

## Search and cache checkpoint

- Manifest confirms mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- `make lean-cache-ensure` EXIT=0: `status=seeded`, `method=clonefile`, donor `/Users/chronoai/trureturing`, `clonefile_attempts=1`, `stamp_miss=null`, project and mathlib both `warm`, missing mathlib oleans=0, archive skipped because project is warm.
- Targeted D5 lookup found no A372018/A371364. Read public signatures and relevant bodies in `CubicNinthPowerSubstitutionModThree`, `HalfScaledReflectionParity`, `ReflectedQuadraticQuarterParity`, `CompositionalIterateCongruence`, and `ConvolutionRecurrenceOddPowersOfTwo`. In particular `convolution_pairing` is general over f but explicitly in ZMod 2; it supplies a modular convolution identity, not the required rational equality. The public `fixed_unique` in CompositionalIterateCongruence is tied to that module's specific step. Generic coefficient agreement and polynomial contraction helpers in the inspected modules are private.
- Mathlib inspected Basic/Substitution/Expand and related API search: `coeff_succ_X_mul`, `X_pow_dvd_iff`, `rescale`, `coeff_rescale`, `rescale_neg_one_X`, `expand`, `coeff_expand_mul` are reusable. No target or generic algebraic fixed-point construction found in searched PowerSeries files. A guessed Rescale.lean path does not exist; actual definitions are in Basic.lean. This failed path is not counted as a search hit.
- External GitHub code searches `A372018 language:Lean` and `A371364 language:Lean` each returned `[]`; arXiv `all:A372018 OR all:A371364` returned totalResults=0. Network capability was actually exercised.
- Opened both OEIS `/internal` pages (HTTP success; raw HTML in attempt-1/sources). A372018 explicitly says “Conjecture: a(2n+1) = 2*A371364().” A371364 specifies the reversion in the brief and offset 0. These two pages contain no proof of the bisection. One-hop cross-references still pending; no global novelty claim.
- Capacity: Recurrence root has 24 Lean files and 48 Blueprint files; do not add at that root. A subdirectory must be selected before implementation.

Proof route refinement before coding: compare s=A(x)-A(-x) directly with 4xB(x²). The proposed elimination is `s(1-xs)^2 = 4x-3x²s`. Its difference factor has constant coefficient 1, so uniqueness can use domain cancellation. This is the same proposed Vieta elimination, with the rescaling bridge performed without constructing C or Laurent series. Define A independently via A=1+xH and the polynomial contraction H=2+x(3H-H²/2+3xH²/2+x²H³/2); define B independently via B=1+x(8B²-3B-16xB³). Neither definition uses the odd identity. These statements remain unverified until Lean checks them.

## Construction checkpoint

- Route returned `D5/S1/Recurrence/Algebraic/CubicOddBisection.lean`, S1/I. Both new Algebraic directories start empty; Recurrence root Blueprint is full and Invariants is already 50, so neither receives an additional file. Route initially rejected `artifact: null` and literal `tag: null`; corrected to `artifact: lean` and empty fields, then EXIT=0.
- Four one-hop sequence cross-references were fetched with curl and their complete internal entries read: A372019, A372020, A059231, A371365. They contain no proof of this bisection. Python urllib's 403 was a transport failure, recovered by curl. A059231's linked papers are second-hop references and remain ASSUMED-UNVERIFIED; they are not asserted to have been opened.
- Mathlib `Polynomial.sub_dvd_eval_sub` read and directly used for coefficient contraction. HenselianRing's inspected primitive requires a monic polynomial and a quotient simple-root lift; no direct ready-to-use statement for the present nonmonic series equations was found.
- First actual Lean attempt: `/tmp/a372018-construction.lean`. The generic coefficient agreement, contraction, stabilization and fixed-equation lemmas elaborated without errors. The two equation proofs failed because ring treated unfolded polynomial arguments and rational C constants as distinct atoms. Those errors are implementation goals, not mathematical obstructions.
- Preserve the verified construction lemmas in the module now. Before the next test, rescale A=1+2xH; the independent contraction becomes H=1+x(3H-H²+3xH²+2x²H³), removing rational constants. B's contraction is unchanged.

Both independent definitions and their exact equations now pass `lake env lean D5/S1/Recurrence/Algebraic/CubicOddBisection.lean`, EXIT=0 (warm tree). `A_equation` proves the constant 1 and original cubic; `B_equation` proves the constant 1 and original normalized reversion equation. No odd-index relation is present in either definition. The earlier ring failure is resolved by integer rescaling and separate polynomial evaluation lemmas. Uniqueness and elimination remain to implement.

## Unbounded identity verified

`lake env lean D5/S1/Recurrence/Algebraic/CubicOddBisection.lean` now EXIT=0. All five public theorems (`A_equation`, `B_equation`, `A_unique`, `B_unique`, `odd_coeff_identity`) have exactly the standard axiom set propext/Classical.choice/Quot.sound. The full natural-number quantified identity is proved, not inferred from a finite prefix.

The Vieta route is now kernel-verified without Laurent series: subtract the cubic equations, cancel u-v using constant coefficient 2, derive `uv(1-x(u+v))+1=0`, and eliminate uv. The difference factor for the resulting sum equation has constant coefficient 1; comparison with 4xB(x²) follows. No use of invertibility of x, of u+v, or of a zero-constant series occurs. A_unique cancels a factor of constant coefficient -2; B_unique cancels a factor of constant coefficient 1.

Two local proof errors were repaired before the successful check: an expansive `neg_pow` simp expression exceeded recursion depth (replaced by map simplification and ring-based linear combination), and a no-progress `simp` became `simp only [map_ofNat]`. These were elaboration errors; the final printed axiom sets have no sorryAx.

Project make gates, Scribe, freeze, and PR remain outstanding; this checkpoint does not claim them complete.

## Documentation and companion API checkpoint

- Added `odd_coeff_identity_of_equations`, the direct API for arbitrary witnesses of the original equations. It consumes A_unique, B_unique, and odd_coeff_identity; the definitions and all six public theorems pass the warm file check with only standard axioms.
- First project `make lean` EXIT=0, 47.264812708 seconds, 12832 jobs. Log and JSON receipt: attempt-1/make-lean.log and make-lean.receipt.json. The arbitrary-witness companion was added after the target module compiled in that run, so a final project build is still required.
- Scribe source now describes all eight public declarations and the polynomial elimination in mathematical terms. Two Library notes attribute each independent equation and the conjecture. Both include `## Verified locator` with the exact frontmatter URL and `doi: null`; no source is credited with the new proof.
- Library/Recurrence capacity before addition: 37 files, after addition 39. Algebraic has one Lean file and will have two Blueprint files after emit. `generality: I` records the particular two OEIS series within the existing Recurrence/S1 domain, consistent with the route result.
- Opened the reversion index linked directly from A371364. It is an index rather than a bisection proof. The previously read four sequence references also contain no such proof; papers linked by A059231 are second-hop and not read. Search conclusion: not-found-in-searched-scope, not a claim of global priority.

## Per-theorem accounting

Module prefix: `D5/S1/Recurrence/Algebraic/CubicOddBisection`.
Direct frozen dependencies (GID + statement_id) are `[]` for every declaration: this module imports only pinned Mathlib modules, no D5 module. The incoming Mathlib theorem `Polynomial.sub_dvd_eval_sub` is used directly, not reimplemented. Local declarations below are candidate-module dependencies, not pre-existing frozen nodes.

| Public theorem | proof_shape | escape_witness | admission_basis | Live local dependencies / obligation |
| --- | --- | --- | --- | --- |
| A_equation | content | fixed_equation, supported by approximation_stable | escape-witness | odd_coeff_identity → odd_series_identity → A_equation; realizes the original normalized cubic |
| B_equation | content | fixed_equation, supported by approximation_stable | escape-witness | odd_coeff_identity → odd_series_identity → B_equation; realizes the original normalized reversion equation |
| A_unique | bind-only | null | escape-witness (module companion, not independent admission) | odd_coeff_identity_of_equations → A_unique; original unique-branch obligation |
| B_unique | bind-only | null | escape-witness (module companion, not independent admission) | odd_coeff_identity_of_equations → B_unique; original unique-reversion obligation |
| odd_coeff_identity | content | cubic_pair_sum | escape-witness | odd_coeff_identity → odd_series_identity → cubic_pair_sum; the requested unbounded equality |
| odd_coeff_identity_of_equations | bind-only | null | escape-witness (module companion, not independent admission) | odd_coeff_identity_of_equations → A_unique, B_unique, odd_coeff_identity; the same equality for arbitrary equation witnesses |

The two definitions A and B are constructions, not public theorems. No definition relates their coefficients. The companion proof explicitly consumes both uniqueness results on its live rewrite path; they are not inserted as unused proof terms.

For A_equation and B_equation, the four witness conditions are:

1. Closure: each directly calls fixed_equation; that proof uses fixed_agree, step_agree, and the induction in approximation_stable.
2. Not a frozen projection: no frozen D5 theorem supplies these series or their equations. The new diagonal construction proves stabilization for arbitrary degree using polynomial divisibility and induction. The direct Mathlib divisibility instance supplies only the contraction step, not a fixed point.
3. Not definitionally equivalent: fixed_equation is a general fixed-point statement for arbitrary c and polynomial p, whereas A_equation is a cubic branch equation and B_equation is a normalized reversion equation. approximation_stable compares two finite iterations at arbitrary degree; it is neither final equation nor an alias of it.
4. Live: the equality for the constructed series is multiplied into each original equation. Without stabilization/fixed_equation the definitions alone do not yield those equations. No discarded conjunction component is used as a witness.

For odd_coeff_identity, the four witness conditions are:

1. Closure: odd_coeff_identity uses odd_series_identity, which directly calls cubic_pair_sum. The eliminated equation supplies the first input of sum_equation_unique.
2. Not a frozen projection: the two original equations do not supply a relation between the odd part and the other series. cubic_pair_sum compares distinct roots, cancels their nonzero difference, derives the product relation, and eliminates the product to lower the problem to a unique sum equation. No inspected frozen or Mathlib theorem provides this elimination or the bisection.
3. Not definitionally equivalent: cubic_pair_sum concerns the sum of two arbitrary roots with nonzero constant difference. It has no odd coefficient, no B, and no index n; it is not a restatement of the coefficient equality.
4. Live: the eliminated equation is necessary to identify A(X)-A(-X) with 4XB(X²). Removing it leaves no first equation for sum_equation_unique. The comparison equation from B and the coefficient maps cannot alone identify the reflected A series. All nonzero factors are proved by their constant coefficients; none is assumed.

`computational_content.kind: none`: all six public results are unbounded algebraic series statements or their uniqueness/parameterized companions. Iteration is an infinite coefficientwise construction with a proof for arbitrary degree; there is no bounded enumeration, finite certificate, numeric reduction, or checker. Other utility fields are not-applicable(kind=none). Header is exactly `utility: none`.

`question_answered`: the corrected A372018 conjecture in the user's brief and this report's opening preregistration. `dominating_theorem_search`: not-found-in-searched-scope; ordered D5, pinned Mathlib, GitHub/Lean and arXiv/OEIS receipts above. No theorem is reported novel merely because the name has not appeared.

## Final-gate repair checkpoint

The next `make lean` returned EXIT=2 after 11.503860209 seconds: Scribe C# helper `D(k)` expects byte, but Pow accepted int (CS1503, line 95). This occurred before the Lean report step; that step did not run. Changed the helper's parameter type to byte; literal exponents 2 and 3 remain unchanged. No mathematical statement or proof changed. Re-run the ordered gates on the repaired documentation.

Pre-PR duplicate lookup against `origin/dev=d59adb46d4703e7fdc7ef7569c5c0919247cc87a`: `git grep -P 'A372018|A371364|odd_coeff_identity|CubicOddBisection' origin/dev -- D5` had no matches (exit 1). Separate `git merge-tree --write-tree HEAD origin/dev` EXIT=0, tree `8fd353645fedccbeb1beec5ce838175b31c05a87`; no conflicts or deleted target paths.

## Final Lean and elaborated dependency receipts

Final `make lean` on the complete six-theorem module: EXIT=0, 29.370193542 seconds, 12832 jobs (attempt-1/make-lean-final-v2.log and .receipt.json). The target module was rebuilt and each public theorem printed only propext, Classical.choice, Quot.sound. The repaired Scribe source also compiled. No sorry, private axiom, native_decide, or forbidden governance terms were found in the Lean/Scribe sources; `git diff --check` passed.

A separate warm Lean audit imports the built module and inspects `Lean.getEnv`, `ConstantInfo.value? (allowOpaque := true)`, and `Expr.getUsedConstants`. Twelve required direct edges all passed, EXIT=0, log attempt-1/dependencies.log: odd_coeff_identity→odd_series_identity; odd_series_identity→cubic_pair_sum/sum_equation_unique/A_equation/B_equation; A_equation/B_equation→fixed_equation; fixed_equation→fixed_agree→approximation_stable; odd_coeff_identity_of_equations→A_unique/B_unique/odd_coeff_identity. These are elaborated proof-body edges, not textual grep counts. The live-path analysis above additionally checks how those results are consumed; a constant edge alone does not prove liveness.

The canonical report currently plans delta recheck of two added modules relative to the seeded report (`changed=0 added=2 removed=0 recheck=2`), and its cache receipt is `status=present`, both layers warm, `stamp_miss=null`. Final report/emit/Scribe results still pending.

## Canonical report, projection, and content checks

- `make lean-report`: EXIT=0, 62.721623375 seconds. Canonical file `.lake/build/stratalint/raw-lean-report.json`, SHA-256 `0056f8dee33c3e29bf569680964b71f70da28c815bb4202f7618011ac36f917d`; input address `sha256:d4dd224d860b7541ce69d925cf8e1ffcedfed051cc72ebb51733f2d669442fe1`.
- The extracted target module report contains 47 declarations, including compiler-generated declarations. Every axiom set is a subset of propext/Classical.choice/Quot.sound; nonstandard axiom findings: `[]`.
- `make emit`: EXIT=0, 56.726954417 seconds. Read the complete generated Blueprint: all eight public declarations and the polynomial proof explanation are present.
- `bash tools/scripts/workflow/scribe-content-checks.sh .lake/build/stratalint/raw-lean-report.json "" d59adb46d4703e7fdc7ef7569c5c0919247cc87a`: EXIT=0, 23.380623542 seconds. Projections and describe-report checks passed; real KaTeX markdown check: judged=1, formulas=8, red=0. Existing Library notes emitted offline DOI observations, not red findings; this does not claim online verification of those unrelated notes.
- A follow-up lookup used a nonexistent `tools/make` directory and returned a path error; the actual canonical targets were located in the root Makefile. No missing-path result is counted as evidence of absence.

Canonical public theorem statement IDs:

| Theorem | statement_id |
| --- | --- |
| A_equation | sha256:8470bdb33de2978141512b0acc4fe6b40514712775adc8def9f9250519ff3f5b |
| B_equation | sha256:289e9bdcfda14c30a2532f2aec923c20f20afd9050fa7cf7e71156b00cdc51c7 |
| A_unique | sha256:1c0955d2f71946554977a61f2f99f70b1713f3f631e9760dccb4ce1ab16b612e |
| B_unique | sha256:e05106d3de9c53083639ba077dfa36a5663093ad31b8773b3293f7b5ab921099 |
| odd_coeff_identity | sha256:3e5b90f6904debab2ee97f02d236b8a5b05d83ebd55546acf35867e9d1bbaa49 |
| odd_coeff_identity_of_equations | sha256:e917c0de71127960a2c74e2a18fdf27cf72860c9b4b21bfacd42b4fa19c1c0b6 |

Freeze and PR remain outstanding at this checkpoint. No theory volume, atom, or finite-instance theorem was added.

## Freeze receipt

`make deposit-uncovered GID=D5/S1/Recurrence/Algebraic/CubicOddBisection.odd_coeff_identity BASE=d59adb46d4703e7fdc7ef7569c5c0919247cc87a`: EXIT=0, 96.362377 seconds. It reused the canonical report above, passed deposit-header-check, emitted zero changed Blueprints, and ran `ledger-align --add` with added=1, conflicts=0. Final receipt: `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED ... reason=NO_ATOM`.

Read back both generated freeze files. Module statement pin: `sha256:2ea92bfb8192b9d99d1f527e7b71c2323eb55698e9a781a9af036f6356ebfabf`; accepted event: `sha256:53528609e1cc3e83dd7ad90ad15d2a68fec6344581bbf294b29eeb8d3bf0874e`; prerequisite frozen node IDs: `[]`. The main theorem's declaration statement ID matches the table above. These two files are committed together. No Lean source changes after freezing.

The implementation PR will target dev and remain open for review, as specified by the user's implementation-stage stopping criterion. No merge or independent review is claimed.

## PR delivery checkpoint

Canonical `make pr-open HEAD=lane/math/a372018 MESSAGE=<attempt-1/pr-message.md>` created PR **#6733** against dev. Implementation and freeze commit `96e0eb106d` was pushed successfully before creation. The canonical watcher initially observed OPEN with three required checks not yet registered; this is a pending observation, not a red result or a claim of green CI. The worker continues tracking the required verdict and records the final observed head/check states in the runner-owned result envelope. The PR body contains the full provenance disclosure and links to this report.

Local final gates all passed in the prescribed order; no new Lean changes followed them. No global novelty, finite-prefix proof, independent review, atom coverage, or merged status is claimed. Final worker-owned artifacts are `result.json` and `completion.sentinel` under the exact attempt directory specified by the user, published by temporary-file rename after final verification.

After PR creation, fetched dev at `5902f61ed734121288ea3ee8b2ad33f11605afbb`. The same exact D5 duplicate search again returned no matches (exit 1). `git merge-tree --write-tree HEAD origin/dev` returned EXIT=0, tree `d7d568088036012fe4516acc9aba37e9bdbec47b`, with no conflicts. The original implementation/gate base remains the immutable d59adb46d4703e7fdc7ef7569c5c0919247cc87a. These post-creation checks do not change that historical receipt. A report-only push superseded the first CI run; the cancelled predecessor is not a failed proof check. The final runner envelope records the required checks for the final pushed head.
