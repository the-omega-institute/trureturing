# A398581 implementation, attempt 1

## Provenance and scope

Codex primary worker, using the `lean4` skill; no delegated implementation or independent review yet. User-supplied orchestrator computations are reported evidence, not computations repeated by this worker. Tier 1. Target: for positive strictly increasing natural solutions of `5xyz = k(yz+xz+xy)`, a lexicographically least solution whose third coordinate is not maximal implies `k % 5 = 1`. No converse and no universal solvability claim.

Worktree `/Users/chronoai/trureturing-a398581`, branch `lane/math/a398581`; immutable starting base `343718ed191002a4708ccf381081f9b0c7a58e1a`. Toolchain `leanprover/lean4:v4.33.0`, mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` read from repository configuration.

## Preregistered proof route

The proposed escape witness is the integer comparison of the least solution against solutions with larger first coordinate, using the small residual numerator `5x-k` in residues 0, 2, 3, 4. This remains ASSUMED-UNVERIFIED until proved. A non-1-residue counterexample stops the positive route. A finite check, or residue 4 alone, does not fulfill the target. No theory volume or atom will be created; any eventual freeze uses the existing uncovered deposit route.

## Search receipts

- D5: `rg -n -i 'A398581|egyptian|unit.fraction|erdos.straus' D5`. No A398581 statement found. Read all declarations of `ErdosStrausModularWitnesses`, `ErdosStrausResidueReduction`, and `PrimaryPseudoperfectPorts`, including their general public interfaces. The first two concern numerator 4 existence/scaling; the third concerns prime reciprocal sums and prime-extension identities. None supplies ordered numerator-5 extremality or a general comparison for arbitrary three-denominator solutions. A prose-only `SingleContextVisibleRemainderDimension` match is unrelated.
- Pinned mathlib and external search: pending. No search-complete claim.

### Search and cache update

Pinned mathlib same keyword query: only three fractional-ideal text matches, no ordered reciprocal-triple extremality theorem. Initial local query preceded cache materialization and returned missing-directory; it was rerun after successful ensure. GitHub code search `A398581` and `"Egyptian"`, both restricted to extension Lean and limit 20, returned `[]`. arXiv API `all:A398581` returned `totalResults=0`. These are bounded searches, not global absence claims.

Opened and read all sequence content of `https://oeis.org/A398581/internal` with curl. It explicitly calls the target a conjecture, records the k=11 comparison, states residue-4 optimality for q>=1, and gives two sufficient infinite progressions inside residue 1. Its Python is finite enumeration, not an unbounded proof. Direct-reference downloads via Python urllib returned HTTP 403; a curl retry for A257843 succeeded, and complete text retrieval is being continued. The supplied triage review of those references remains attributed to the user until independently read.

`make lean-cache-ensure` EXIT=0; `LEAN_CACHE`: status=seeded, method=clonefile, donor=/Users/chronoai/trureturing, clonefile_attempts=1, stamp_miss=null, project_olean_state=warm, mathlib_olean_state=warm, mathlib_missing_olean_files=0. Full receipt: attempt-1/cache.log in the runner artifact directory.

### Route refinement before Lean probes

For `a=5x-k`, `b=kx`, and `d=ay-b`, the equation implies `d>0` and `az=b+b²/d`. Thus a lower bound on d bounds z. The difficult residue-2 subcase has first residual a=3 with 3 dividing b, giving a candidate of size approximately b²/9. At the next x, a=8; d=1 would imply `k²=-5 (mod 8)`, impossible for a square. This proposed modular obstruction and the subsequent interval estimates are the refined escape witness, still ASSUMED-UNVERIFIED pending Lean.

Curl retries succeeded for all six direct sequence references A257843, A075248, A075249, A075250, A075251, A257839 and official b398581.txt. Their complete sequence texts were read; the b-file contains the advertised 86 lines and no proof. A257843/A257839 concern numerator 4. A075248 counts numerator-5 solutions; A075249–251 stop after their first solution (`cnt==0`), despite the maximal-z wording, so those programs cannot supply this theorem. No complete target proof was found in this checked scope. Links beyond those direct entries have not been opened and remain ASSUMED-UNVERIFIED.

The first actual Lean attempt proved the integer bounds `0<k`, `k<5x<3k` and positivity of `(5x-k)y-kx`. Two following lemmas initially failed because ordering facts were left inside the `Sol` definition, and one `mul_pos` argument was an inequality rather than a positive difference; these are implementation errors, not mathematical obstructions. Log: attempt-1/bounds-1.log. The correction is being checked.

## General comparison lemmas verified

`bounds-2.log` EXIT=0 verified basic bounds, residual bound, and same-x antitonicity, standard three axioms only. The later `bounds-4.log` verified the near and far inequalities, with one subsequently corrected unknown lemma name (`Int.pow_emod`; use the existing `Int.mul_emod` instead).

The live comparison is: when `5x>=2k`, `25z<=2k(2k+5)`; when `l<=x` and `5x<=2k`, a residual lower bound d and the endpoint bound `kl(kl+d)<=d(5l-k)W` imply `z<=W`. The near estimate uses the nonnegative product `k²(x-l)(k(x+l)-5xl+d)`, not a finite enumeration. Residual 8 excludes d=1 by the square residues modulo 8. These are private general proof helpers on the live path to the target, direct frozen dependencies `[]`, proposed admission `escape-witness`; no standalone freeze requested for them.

Endpoint polynomial inequalities have been proved for residues 0 and 4; residues 3 and 2 use lower bounds `4W>=b(b+2)`, `3W>=b(b+1)` or `9W>=b(b+3)`. The remaining small parameter branches will be private deductions from the residual bound, splitting x only. They do not constitute a separate positive finite certificate or a claim of research progress.

## Target kernel proof

`bounds-6.log` EXIT=0 verified all five parameterized later-x bounds. `bounds-7.log` verified all three candidate constructions and the lexicographic comparison lemma; the small branches required explicit x bounds for `interval_cases`, subsequently added. `bounds-10.log` EXIT=0 verified `first_maximum_separation_mod_five` over naturals, with axioms exactly `[propext, Classical.choice, Quot.sound]`. No sorry, private axiom, or native_decide is used.

The proved statement uses existence of any competing solution with larger z. A maximum-z solution in the user's premise supplies precisely that competitor, so no extra finiteness or maximum-attainment hypothesis is assumed. `IsLexFirst` spells out all three coordinates of the lexicographic order and includes membership in the positive strictly increasing integer-equation solution set.

Additional supporting search: read all public declarations of D5 `OddSquareModuloEight` and `ModThreeNormObstruction`. The former is a natural odd-square divisibility wrapper, not the all-integer obstruction used here. The final proof directly reuses pinned Mathlib `Int.sq_mod_four_eq_one_of_odd` (and `Int.even_or_odd`) to rule out the residual-8 equality; it does not re-prove that odd-square theorem. No D5 frozen theorem is a direct dependency.

### Declaration assessment

Public theorem `first_maximum_separation_mod_five`: `proof_shape=content`; direct frozen dependencies `[]`; `admission_basis=escape-witness`; `computational_content.kind=none`. It quantifies over all natural parameters and solutions. Private finite x splits only close the small branches of that unbounded theorem.

The named escape witness is `near_bound`, together with its live endpoint applications in `later_two_divisible`. Clause (i): these declarations occur in the elaborated chain through `first_maximal` to the public theorem; kernel axiom output confirms successful elaboration (a detailed constant-closure receipt will accompany formal inspection). Clause (ii): their interval and endpoint inequalities are new estimates, not instances or projections of frozen prerequisites (there are none). Clause (iii): the intermediate z bound has an endpoint inequality and residual premise, and is neither definitionally equal to nor a restatement of the modulo-five conclusion. Clause (iv): the q>=11, residue-2 divisible branch uses the bound to compare every later x with the constructed candidate; removing it leaves that branch unproved. The d>=2 obstruction at residual 8 is also actively used for its adjacent x. No irrelevant component is attached and discarded.

Before the formal write, directory counts: D5/S3/Arith/Congruence=21 files; mirrored Blueprint bucket=42; Library/notes=23. Arith is registered at S3. Generality I and utility none describe the unbounded, fixed-numerator arithmetic theorem. Canonical route requested for EgyptianFiveFirstMaximum.

## Formal delivery gates

Canonical route returned `D5/S3/Arith/Congruence/EgyptianFiveFirstMaximum.lean` and its seven-line skeleton (attempt-1/route-2.log). The first route call rejected an absolute manifest path; the successful call used repository-relative `build/a398581/formal-manifest.json` and artifact=lean. The verified scratch proof has been moved to that formal module; its previous versions remain in Git, not as a duplicate theory source.

First `make lean`: EXIT=2 in 2.992s due to a missing parenthesis in the new Scribe formula. Corrected by naming the formula components. Second `make lean`: EXIT=0 in 79.090s, 12845 jobs; the new module's build was reported as 17s and its axiom closure as the standard three. Receipt `make-lean-2.json`, log `make-lean-2.log` in attempt-1. `LEAN_CACHE` status=present, method=none, stamp_miss=null, project_olean_state=warm, mathlib_olean_state=warm, missing mathlib oleans=0. The prior seed receipt is preserved above.

The code's active capacity constants are hard=1000 and soft=800 lines (`RepositoryRules.Structure.cs`); the formal module has 673 lines, below both. Spec A5 still mentions 400 lines; this discrepancy is disclosed and no capacity rule is changed. The former report proof was removed after migration, not frozen or ingested.

## Verification and remaining obligations

No Lean attempt run yet. No theorem frozen. Build/cache receipts, exact declaration classifications, and final outcome will be appended after each completed unit.

## Unclaimed

No all-k solvability, converse, universal maximality theorem, literature novelty beyond checked sources, or independent review consensus is claimed. All unopened external pages and the brief's proposed proof route are ASSUMED-UNVERIFIED.
