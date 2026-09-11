# OEIS A374911 implementation record

## Current result

The target theorem and the unrestricted classifications of values one, two,
and three are proved from the original guarded recursion. All local delivery
gates passed and the module is frozen without an atom. PR:
https://github.com/the-omega-institute/trureturing/pull/6746 (open, not merged).
The chronological checkpoints below preserve earlier pending states and failed
attempts; this section and the final delivery receipt supersede those states.

## Origin and scope

2026-09-10. Skill: `lean4`; implementation by the Codex worker in the supplied
`consensus-rnd/sshx/a374911-impl-0910/attempt-1` context. One implementation
worker, no independent review performed by this worker. User-supplied numerical
checks and the triage route are attributed to the user, not independently verified here.

Branch: `lane/math/a374911`. Immutable starting base:
`24279623ef5253194f6c64ee3b3b627e62e3df50` (`origin/dev` at start).

Target: define `seq 0 = 1` and, only for positive `n`,
`seq n = seq (2^n % n) + seq (3^n % n)` by well-founded recursion;
prove `seq n = 4 ↔ n = 3 ∨ n = 9` for every natural `n`.

Tier: first tier, as explicitly assigned. The claim of no published proof is
user-supplied pending the worker's source inspection. No new theory volume,
ingestion, or atom will be created. Intended atom-free freeze: `ledger-align --add`.

## Preregistered route and stopping conditions

The proposed escape witness is the arithmetic exclusion of higher powers of
three: from `2^(3^k) % 3^k = 2^j < 3^k`, force `k ≤ 2` using multiplicative
order/LTE and growth. Its prerequisites are the recursive classifications of
values one, two, and three, and the smallest-prime-factor exclusion of
`n > 1 ∧ 2^n % n = 1`. This is the route supplied in the brief and is currently
`ASSUMED-UNVERIFIED`, not a proof claim. If either critical arithmetic step
resists a concrete Lean attempt, follow the user's stop condition and deliver
a note with the exact remaining goal.

## Search receipts

- Read the complete `CLAUDE.md` (779 lines) in chunks and `agents/CONTEXT.md`.
- D5 coarse search: `374911|pow.*mod.*eq_one|minFac|orderOf.*dvd|pow_sub_pow|pow_two_sub_one_ge`.
  No exact A374911 statement found. Hits include general order and smallest
  prime factor lemmas; their relevant public interfaces still need inspection.
- The attempted path `tools/scripts/lean.sh` does not exist. The canonical
  Lean command will be read from `Makefile`; no bare cold Lake command was run.

## Validation

No Lean attempt or build has yet run. No theorem is claimed proved or frozen.
`make lean` exit code, elapsed time, cache receipt, report/emit/deposit and
Scribe content-check results will be recorded as they are produced.

## Declaration accounting

No public declarations yet. For the target, pending proof:
`proof_shape: unassessed`; direct frozen dependencies: not yet determined;
`escape_witness`: proposed arithmetic exclusion above;
`admission_basis`: proposed `escape-witness`, not yet established.
The four conditions of CLAUDE 3.2 will be checked against the final proof.

## Not claimed

No all-natural classification, independent numerical verification, exhaustive
literature search, successful build, freeze, PR, or independent review is claimed.
Pages not actually opened are `ASSUMED-UNVERIFIED`. Finite checks will not be
reported as progress on the unrestricted theorem.

## Search and cache checkpoint

- `make lean-cache-ensure` EXIT=0, real 18.70 seconds. `LEAN_CACHE`:
  `status=seeded`, `method=clonefile`, donor `/Users/chronoai/trureturing`,
  `clonefile_attempts=1`, `stamp_miss=null`, both project and Mathlib warm,
  missing Mathlib oleans=0. Full log is in the attempt directory.
- Manifest confirms Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Read A091259's complete public API, the general affine-conjugacy and
  invariant-set order signatures in CyclicPlaneTwelveMultiplierObstruction,
  and all public theorem names in the minFac search hits. General lemmas there
  concern divisor pairs, Jordan cototients, or invariant finite sets; no exact
  primitive for this recurrence. Read GoldenCell5040Congruence in full: its
  order-to-congruence helper is private, and its public theorem is the six-element
  5040 cell. No reusable exact public hit was found in this searched scope.
- Mathlib search/read hits: `Nat.coprime_of_lt_minFac`, `Nat.dvd_prime_pow`,
  `ZMod.orderOf_dvd_card_sub_one`, `orderOf_dvd_iff_pow_eq_one`,
  `padicValNat.pow_sub_pow`, `padicValNat.pow_add_pow`,
  `padicValNat.pow_two_sub_one_ge`, `padicValNat_dvd_iff_le`,
  `Nat.ModEq.pow_totient`, `Nat.totient_prime_pow_succ`. These will be reused.
  The guessed Pseudoprime.lean path was absent; located and searched FermatPsp.lean.
- Authenticated GitHub code search `A374911 language:Lean`: total_count=0.
  arXiv API `all:A374911`: totalResults=0. This establishes network access and
  bounded non-hits, not global absence.
- Opened the full OEIS text entry A374911: it explicitly asks “Are 3 and 9 the
  only solutions to a(n) = 4?” The original recurrence and zero case match.
  Opened its three direct xrefs A000079, A015910, A066601. No target proof in
  those entries. The first broad A000079 display was truncated; the missing
  relevant links were read separately.
- Followed A015910 to A036236, which explicitly gives Max Alekseyev's
  smallest-prime-divisor proof of `2^n mod n ≠ 1` and Firoozbakht's formula
  `2^(3^k) = 3^k - 1 (mod 3^k)`. These are known prerequisites, not novelty claims.
- Opened Coons–Winning's “Powers of Two Modulo Powers of Three” landing page
  linked from A000079. Its abstract concerns finer mod-six structure and
  Stoneham normality. Full paper not yet read, `ASSUMED-UNVERIFIED`.
- Spec A5.1 gives `utility: none` for a noncomputational general classification.
  Arith is registered at S3; proposed Congruence bucket has 20 files before addition.

## Preregistered route revision 2 (before Lean proof)

The newly read A036236 formula shortens the proposed higher-power exclusion.
Use the odd-prime **addition** LTE (`padicValNat.pow_add_pow`) to obtain
`3^k ∣ 2^(3^k) + 1`, hence its remainder is `3^k - 1` for positive `k`.
Then classify `3^k - 1 = 2^j` by parity/mod-eight and factorization (or the
two-adic LTE already searched). This is a revision of the preregistered
arithmetic witness, recorded before trying it. The original subtraction-LTE
route remains unverified and is no longer the implementation plan. The user’s
stop condition at smallest-prime exclusion or LTE remains in force.

## Critical arithmetic checkpoint

The warm Lean check of `attempt-1/Critical.lean` exited 0. Both
`two_pow_self_mod_ne_one` and `three_pow_dvd_two_pow_add_one` were kernel
checked, with only propext, Classical.choice, Quot.sound. The smallest-prime
exclusion and addition-LTE step both succeeded; the stopping condition did
not trigger. They are saved as private helpers in the routed module. This
checkpoint does not yet prove the sequence classification.

The route command accepted Arith/Congruence/PowerResidueRecursionFour with
generality I. Its first call rejected an absolute manifest path; retry used
a repository-relative `.lake/a374911-route.json` and returned the canonical
GID and seven-line skeleton.

## Recursive classification checkpoint

The warm file check of the routed module exited 0 with no warnings. `seq` is
well-founded recursion on n, with both recursive calls guarded by n ≠ 0 and
termination established by `Nat.mod_lt`. The unbounded theorems `seq_eq_one`,
`seq_eq_two`, and `seq_eq_three` are proved; all three axiom outputs are exactly
propext, Classical.choice, Quot.sound. Values one/two use strong-induction
positivity and coprimality; value three uses the least-prime exclusion and
Euler's totient theorem for every positive power of two. This is symbolic
progress, not finite enumeration. Target value four is still outstanding.

A first value-three check had one local nested `by`/semicolon scoping error
at the k=0 contradiction (and therefore reported sorryAx on that failed
declaration); it was repaired with a separate proof block. The successful
second check has no sorryAx. Log: attempt-1/seq-three-check.log.

Route refinement within revision 2, before trying the last Diophantine step:
for even k, two-adic LTE gives j = 2 + v₂(k), hence 2^j ≤ 4k; compare with
3^k - 1 > 4k for k ≥ 3. For odd k, reduce modulo four to force j=1.
This supplies the stated parity/LTE alternative without factoring two
adjacent prime powers. No implementation of this final step has yet run.

Additional search: D5 arithmetic/Factorization and Mathlib NumberTheory
searches for mixed two/three powers found factorization identities and
polynomial Fermat–Catalan, not this integer exponential equation. Read the
Coons–Winning introduction and main proposition in its downloaded TeX; it
classifies bi-periodic subsets. The remainder of its proof and unrelated
second-hop references are not claimed read.

## Higher-power exclusion checkpoint

The warm main-file check including `two_pow_self_mod_three_pow`,
`three_pow_gt_linear`, and `three_pow_sub_one_eq_two_pow` exited 0.
Log: attempt-1/arithmetic-check.log. Addition LTE gives the exact remainder;
two-adic LTE and exponential growth exclude every even k ≥ 3, and reduction
modulo four excludes every odd k ≥ 3. Both critical arithmetic boundaries
have now passed Lean. Only assembly of the value-four theorem remains.

Broadened searches read Mathlib Archive/Imo/Imo2025Q3.lean and
Archive/Imo/Imo2005Q4.lean completely. The former has a similar local LTE
bound in `fExample.apply_le`, but its public statement assumes `IsBonza f`;
the latter treats a different sum sequence. Neither exports the needed
standalone primitive. GitHub code query `"2 ^ n" "minFac" language:Lean`
returned 21 matches. Read Compfiles `usa1982p4.lean` and `imo2000p5.lean`
at 51c8803ed93c0a350d110fffe4c3804b473bba78: their public constructions
and general congruence helpers supply no needed primitive beyond Mathlib.
Read `putnam1972a5.lean` in shanjiaming/lean-pl-fix at
229f898bd9bc4a7894cfadde622afe814590b8e9. It states the related integer
nondivisibility result but is a raw proof dataset fragment, without imports;
its proof has repeated steps that lose the minFac relation. It has not been
compiled here and is `ASSUMED-UNVERIFIED`, not admitted as a usable library
proof. The known mathematical prerequisite is attributed to A036236.
Unopened search hits and fork copies remain `ASSUMED-UNVERIFIED`.

## Main theorem checkpoint

`a374911_eq_four (n : ℕ) : seq n = 4 ↔ n = 3 ∨ n = 9` passed the warm
Lean check (EXIT=0). Log: attempt-1/main-theorem-check.log. All four public
theorems have exactly `[propext, Classical.choice, Quot.sound]` as their
printed axiom closure. The definition is still the guarded original recursion.
The proof excludes left summand values one and two, forces n to be a positive
power of three, and applies the higher-power exclusion above. The two reverse
cases reduce privately in this theorem; no finite-instance declaration is
exported. No full-project build, freeze or PR has yet been claimed.

### Final declaration accounting

All four public theorems have `proof_shape: content`,
`direct_frozen_dependencies: []` (no imported D5 modules), and module
`admission_basis: escape-witness`. The definition `seq` is the common recursive
object, not a theorem. Its helper declarations are private.

| Public theorem | Named escape_witness | Consumer → prerequisite |
| --- | --- | --- |
| `seq_eq_one` | `seq_pos`: positivity for every natural index by strong induction | `seq_eq_one → seq_pos` |
| `seq_eq_two` | `seq_pos`: positivity forces both recursive summands to one | `seq_eq_two → seq_pos` (also through `seq_eq_one`) |
| `seq_eq_three` | `two_pow_self_mod_ne_one`: smallest-prime/order exclusion for every n > 1 | `seq_eq_three → two_pow_self_mod_ne_one` |
| `a374911_eq_four` | `three_pow_sub_one_eq_two_pow`: k > 0 and 3^k − 1 = 2^j force k = 1 or 2 | `a374911_eq_four → three_pow_sub_one_eq_two_pow` |

CLAUDE 3.2 four-condition audit, individually applicable to the witnesses named
in the table: (i) each is invoked in the elaborated proof's transitive constant
closure; `seq_pos` is consumed in the arithmetic comparison, the order exclusion
in the summand contradiction, and the final exponent restriction in the final
case split. (ii) Positivity requires a new strong induction on the recursive
function; the order exclusion constructs a least-prime contradiction; the
exponent restriction combines parity, two-adic LTE and a new inductive growth
bound. No frozen premise provides these facts by projection or instantiation.
(iii) Positivity, a modular non-equality, and the mixed-power restriction are
neither definitionally equal to their consuming classification nor restatements
of it. (iv) The mentioned comparisons, contradiction and case split are live
uses, with no discarded pair component or dead local fact; removing each named
witness leaves the stated branch unsupported by mere rewriting of frozen facts.
Mathlib's general results are cited directly; they supply arithmetic ingredients,
not any of the recursive classifications.

`utility: none`: every public theorem quantifies over all natural indices and
classifies a level set. No public result is a bounded enumeration, checker,
numeric reduction, or certified finite instance. The defining function is a
well-founded recurrence; numerical reverse branches are local parts of the
unbounded theorem. All other utility fields are not-applicable(kind=none).

Pre-Blueprint capacity check: Congruence has 40 files (adding source and emitted
mirror gives 42); Library/Arith already has 48, so no new file will go there.

## Publication source checkpoint

Added a five-node Scribe source (definition and four classifications), plus
two source notes in Library/ArithSums, whose prior capacity was 7 files.
Both notes contain a Verified locator subsection with the exact frontmatter
URL. A036236 is correctly identified as the least inverse of A015910, not
the residue sequence itself. The proof's provenance is `repo-derived`, with
acknowledgements for the source question and known arithmetic ingredients;
there is no claim that the complete proof is literature-attested or globally
novel. The production Scribe checker explicitly rejects suspected-novel nodes
(DescribeContentGovernance.cs); `FromRepo` accurately records the proved
repository derivation, while the bounded literature non-hit remains in this report.

First `make lean`: EXIT=2, real 11.58 seconds. Its cache preflight compiled
the concurrently added Scribe file and found CS1503: `D` expects a byte but
`LevelFormula` accepted int. Changed that helper parameter to byte, matching
all four constant call sites. This was a narrative-source compile failure
before the Lean build, not a failed mathematical proof. Full build retry pending.

## Full build checkpoint

`make lean` retry EXIT=0, real 62.70 seconds (user 81.30, sys 43.30),
12,838 jobs in this warm worktree. Log: attempt-1/make-lean-retry.log.
The initial cache receipt remains the explicit successful `make lean-cache-ensure`
receipt above; the canonical build used `lean-cache-run.sh` and its cache writer.
The build output includes pre-existing warnings in other modules. The four
A374911 theorem axiom closures are the standard set and the target file contains
no `sorry`, private axiom, or `native_decide`.

Before PR, fetched origin/dev and re-ran `git grep -P` over its D5 for
`A374911|a374911_eq_four|PowerResidueRecursionFour`: no hit. The remote base is
still 24279623ef5253194f6c64ee3b3b627e62e3df50. Local D5 search finds only
this module. No competing exact implementation was found in either snapshot.

## Report and projection checkpoint

`make lean-report` EXIT=0, real 58.12 seconds. Canonical report SHA-256:
`1516bcdde4c0c6bc721f94b0add1ac243f72f4110d2474922e2c7cdb28900948`.
Its module record confirms only Mathlib/Init imports and the standard axiom
set for each included theorem. Extract: attempt-1/module-lean-report.json.
`make emit` EXIT=0, real 50.83 seconds; it generated exactly one changed
Blueprint document. Read the entire emitted document and checked its four
quantified classification formulas and the guarded recursive definition.
Logs: attempt-1/make-lean-report.log and attempt-1/make-emit.log.

The full-build `LEAN_CACHE` line additionally records `status=present`,
`method=none`, `stamp_miss=null`, project/Mathlib `warm`, and zero missing
Mathlib oleans. No cold bare Lake operation was used.

## Scribe content checkpoint

The exact requested `scribe-content-checks.sh` call against base
24279623ef5253194f6c64ee3b3b627e62e3df50 exited 0 in 23.63 seconds:
`DESCRIBE_STATUS ... nodes=10427 suspected_novel=0 ... red=0`, and
`markdown: judged=1 formula(s)=5 red=0`. No locator failure occurred.
The observations and existing OPEN projection messages are not assertions
about this module or additional successful theorem claims. The wrapper's
change selection did not require `projections --check`; that subcommand is
also being run explicitly so all three named checks have local receipts.
Log: attempt-1/scribe-content-checks.log.

The canonical report's included statement IDs for the public classifications:

| Theorem | statement_id |
| --- | --- |
| `seq_eq_one` | `sha256:e4cef3ff396927ef71e44f2084a8c78998f4d5196138289477a588a879d95674` |
| `seq_eq_two` | `sha256:839399b039e4a4390497e695b563e85ab87d472c3a83a265332ca5af8be763ef` |
| `seq_eq_three` | `sha256:ee69f334ca172cabc78035793dde2c35f49597ba74373ad0a2dccbaded2edaee` |
| `a374911_eq_four` | `sha256:e966ef5d9b8179518c3c4faf341adbf26d48fb9aa4c9ef99c500983de8e97cf8` |

The module report also includes private prerequisites and compiler-generated
recursion equations; they are not extra public mathematical APIs or independent
finite-instance freezes. The module has no direct frozen D5 prerequisite pairs.

## Freeze receipt

Explicit `projections --check` EXIT=0, real 7.31 seconds; its log is
attempt-1/projections-check.log. Together with the wrapper receipt this covers
all three requested Scribe subchecks locally before PR creation.

`make deposit-uncovered` EXIT=0, real 83.70 seconds, using the immutable base
and target declaration GID. This canonical no-atom wrapper ran lean-report,
deposit-header-check, emit, and `ledger-align --add`. The latter reported
`selectors_considered=3952 changed=0 added=1 unchanged=3951 conflicts=0`.
The terminal receipt is `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED ... reason=NO_ATOM`.
Log: attempt-1/make-deposit-uncovered.log.

- Module: `D5/S3/Arith/Congruence/PowerResidueRecursionFour.lean`.
- Frozen module statement_id:
  `sha256:01e17f29d71e477eb733c3317b05e837a545493527b41ca198a0f13d58126e27`.
- Freeze event_hash:
  `sha256:866054aa89ab228b3b2807e8812291ad73d3e884d60513d9c47d2db77bf38d82`.
- `prerequisite_frozen_node_ids: []` in the emitted event agrees with the
  reported direct frozen dependencies.
- No source_id, atom_id, ingestion or coverage edge: the result is frozen
  and uncovered, with no claim of atom digestion.
- Final bucket counts: D5 Congruence 21, Blueprint Congruence 42,
  Library/ArithSums 9. `git diff --check` exited 0.

## Final not-claimed scope

No proof of surjectivity, classification of value five, independent numerical
sweep, independent reviewer approval, global novelty, exhaustive literature
search, merge, or atom digestion is claimed. The original subtraction-LTE
route was replaced before its proof attempt; only the explicitly revised
addition/two-adic route is verified. Unopened pages and the uncompiled dataset
fragment remain `ASSUMED-UNVERIFIED`. The user-supplied measurements remain
attributed measurements, not worker-produced numerical evidence.

## PR delivery

Created PR #6746 with `make pr-open HEAD=lane/math/a374911 MESSAGE=...`.
The tool's canonical watcher owns the required-CI wait. Its terminal result
is recorded in attempt-1/pr-open.log and the final worker result envelope;
this commit records PR creation, not a claim of completed remote checks.
No auto-merge was requested. The task's three-state completion criterion is
met as **成**: the unrestricted theorem is proved from the specified recursion,
`make lean` exited 0, there is no sorry/custom axiom, and the PR is open.
Repository merge completion and independent review remain outside this claim.
