# A390148: primitive spherical radii, 3-adic orders

Current status: **成** under the implementation brief: the exact requested
theorem is proved, the project build, canonical report and Scribe content checks
pass, the module is frozen without an atom, and
[PR #6739](https://github.com/the-omega-institute/trureturing/pull/6739) is open.
CI is pending at this report commit; its subsequent result is recorded in the
worker-owned completion artifacts. Sections below are chronological
receipts; early statements marked pending describe their time of writing.

## Provenance and scope

Implementation by the Codex worker using the `lean4` skill, in the runner's
implementation stage. This is a single implementation source, not an independent
review or a multi-model consensus. The supplied orchestrator's enumeration is
reported input, not rerun evidence from this worker.

Branch: `lane/math/a390148`. Immutable starting base:
`462d0a4368ba5a890c5eab619c82437baa88966f` (`origin/dev` at start).
Tier: first tier, the 2025 OEIS conjecture, restricted to the 3-adic clause.

The target quantifies over all positive primitive natural radius quadruples
satisfying `(sum (1/r))^2 = 3 * sum ((1/r)^2)` over the rationals. The proposed
intermediate witness, preregistered in the implementation brief, is that primitive
integer curvatures satisfying `(sum b)^2 = 3 * sum (b^2)` have exactly three
coordinates not divisible by 3. The denominator bridge must establish its own
primitivity. No local valuation classification will be assumed.

Stop conditions: a failed primitive denominator bridge or a located existing
proof changes the delivery to a note. A failed Lean attempt must record the exact
remaining goal. Success requires the full theorem, no sorry/private axiom, the
required local build/content checks and an opened PR.

## Search receipts (ongoing)

1. Read `CLAUDE.md` completely, `agents/CONTEXT.md`, and specification A5/A5.1.
2. `rg -n -i '390148|sphereDescartes|gcd4|Descartes|soddy|gosset' D5`:
   no matches on the starting base.
3. `rg -n 'padicValNat|Finset.*lcm|Finset.*gcd' D5 --glob '*.lean'`:
   candidate modules include `FiniteCompatibleCrt`, `RationalValuationRecovery`,
   `DeeplyCompositeLcmRank`, `TotientNondivisorRecords`, and
   `SumTwoSquaresClassification`. Public interfaces are being inspected for
   general-purpose facts; absence of a same-named theorem is not a reuse verdict.
4. `make lean-cache-ensure` started before any Lake invocation. The worktree had
   no accessible mathlib checkout before this command; cache receipt pending.

External literature status: not yet assessed by this worker. Pages not opened
are `ASSUMED-UNVERIFIED`; the supplied triage is not substituted for inspection.

## Delivery accounting (pending proof)

For `primitive_sphere_radii_v3`, proposed `proof_shape: content`,
`admission_basis: escape-witness`; the intended witness is the primitive integer
curvature mod-3 classification above. These are preregistration, not a claim of
an elaborated proof. Direct frozen dependencies and statement IDs pending.

No new theory volume or atom will be created. The no-atom freeze uses the
repository's uncovered-deposit/`ledger-align --add` path. General infinite
quantification is intended; numerical samples are probes only.

## Unclaimed

No claim about primes congruent to 2 modulo 3, repetition formulas, arbitrary
chains, OEIS column sequences, or the coefficient-2 circle equation A390583.
No claim that the supplied enumeration proves an unbounded statement. No claim
of completed proof, library exhaustiveness, build success or freeze yet.

## Search batch 2 and cache receipt

- `make lean-cache-ensure` EXIT=0: status=seeded, method=clonefile,
  donor=/Users/chronoai/trureturing, clonefile_attempts=1, stamp_miss=null,
  project_olean_state=warm, mathlib_olean_state=warm, missing mathlib oleans=0.
  Toolchain is v4.33.0; mathlib HEAD is
  db584cd6d46c92f209a44c0f1c829460d327499d.
- Read the public statements of the five candidate D5 modules above: finite CRT
  gluing, rational recovery from all valuations, deeply-composite rank bounds,
  totient LCM jumps and two-squares classification do not supply the primitive
  reciprocal-denominator identity or the coefficient-3 congruence. Their general
  public results were inspected, not excluded by topic name.
- Mathlib search for Descartes/Soddy/Gosset found only the polynomial rule of signs.
  Read the full public Finset gcd/lcm API, including lcm_dvd, dvd_lcm, gcd_dvd,
  dvd_gcd, lcm_ne_zero_iff, extract_gcd and gcd_div_eq_one. Read padicValNat.mul,
  div_of_dvd, pow, and divisibility/valuation equivalences. Also found binary
  Nat.div_lcm_eq_div_gcd; it is the opposite quotient identity and does not
  directly establish primitivity of L/r. We will use the general divisibility API.
- Opened https://oeis.org/A390148/internal, revision 23 (2025-11-17), and read all
  fields. The coefficient-3 equation matches exactly. The main comment still
  states the 3-adic clause as observed for 1000 rows and conjectured for infinity.
  Author Charles L. Hohn, 2025-10-26. Its listed links/columns are data or the
  other excluded clauses; their full inspection remains supplied triage evidence,
  not claimed as this worker's independent reading.
- GitHub code search `A390148 language:Lean` and `Descartes sphere language:Lean`
  both returned []. Broader `Descartes language:Lean` returned polynomial rule of
  signs and Apollonian circle-packing files, not the sphere theorem. No third-party
  file is imported or claimed verified on the basis of search snippets.
- Opened https://arxiv.org/search/?query=A390148&searchtype=all : explicitly
  produced no results. Google HTML queries returned only a JavaScript redirect
  page; Bing RSS returned unrelated results and is discarded as search evidence.
  Search capability is available via GitHub, arXiv and direct OEIS inspection;
  generic web-engine searches are not claimed complete.
- dominating_theorem_search: not-found-in-searched-scope. No direct existing
  proof found in these inspected sources; retain first tier, without claiming
  global priority or exhaustive absence.
- Directory counts before Lean creation: D5/S3/Arith has 34 direct files,
  Blueprint/D5/S3/Arith has 58 including projections. Use a new Descartes child
  bucket (0 prior files). docs/reports has 47 direct files including this report.
  No lower AGENTS.md/CLAUDE.md was found under the edited content directories.

## Lean unit 1: the primitive denominator bridge

- Canonical route returned D5/S3/Arith/Descartes/PrimitiveSphereRadii.lean,
  S3, generality I. Seven-line header uses `utility: none` in the specified slot.
- Hot-tree `lake env lean D5/S3/Arith/Descartes/PrimitiveSphereRadii.lean`
  EXIT=0. Proven: positive common multiple, positive integer curvatures,
  curvature times radius equals L, gcd of all curvatures equals 1, and the
  coefficient-3 equation transfers from rational reciprocals to naturals.
- Primitivity proof uses no primitive-radius hypothesis: with d=gcd(L/r_i),
  d divides L and each r_i divides L/d. Thus L divides L/d; positivity and
  Nat.div_lt_self rule out d>1. The conjectured denominator bridge succeeds.
- First compiler diagnostic was ambiguity between root `lcm_dvd` and
  `Finset.lcm_dvd`; fixed with the exact namespace. The quotient divisibility
  API also orders factors as d*r, handled by commutativity. No sorry or axiom.
- Scalar rational bridge uses Nat.cast_div under the proved divisibility and
  nonzero-radius premises, factors L squared through the sums, then casts back.
  Every intermediate natural curvature is positive, excluding valuation-of-zero.
- Additional Mathlib reuse: inspected `ZMod.pow_card_sub_one`; it gives the
  square indicator in characteristic 3 directly, so residue enumeration is
  unnecessary. The next unit will count the nonzero residues from the equation.

## Lean unit 2: exactly three unit curvatures

- Hot-tree file check EXIT=0. The general private lemma
  `curvature_unit_count` takes only an arbitrary natural quadruple, gcd=1,
  and the coefficient-3 equation; it proves exactly three coordinates are
  not divisible by 3. No finite radius range or radius repetition is used.
- Derivation: 3 divides the square of the sum, hence the sum itself. Writing
  that sum as 3*k gives sum(b_i^2)=3*k^2, so its reduction modulo 3 is zero.
  `ZMod.pow_card_sub_one` rewrites each square as its nonzero indicator;
  `Finset.sum_boole` identifies the total with the unit-coordinate count.
  The count is a positive multiple of 3 bounded by 4, hence equals 3.
- Compiler repair: corrected the explicit witness for divisibility of the
  square sum from 3*k^2 to k^2; explicitly unfolded `ne_eq` to rewrite the
  cast-nonzero condition. The successful proof uses no enumeration.
- This is the preregistered intermediate witness. Its application to the
  positive primitive curvatures is the next step toward the radius theorem.

## Lean unit 3: complete requested theorem

- Hot-tree file check EXIT=0 for the full `primitive_sphere_radii_v3` signature.
  `#print axioms` reports exactly propext, Classical.choice and Quot.sound.
  The source contains no sorry, axiom declaration, or native_decide.
- Set e=v3(L). Positivity permits padicValNat.mul on curvature_i*radius_i=L.
  Thus a curvature is a mod-3 unit exactly when its radius has valuation e.
  The unit count gives three such radii. If e=0, the product valuation identity
  would force all four to have valuation e, contradicting the count. The
  complement of this three-element set is a singleton. Primitivity of the
  radii supplies a radius not divisible by 3, which must be that singleton.
- Compiler repair: added the predicate type to an intermediate Finset membership
  proof so its implicit filter could be inferred. No hypothesis was strengthened.
- Public theorems (exactly one): `primitive_sphere_radii_v3`.
  proof_shape: content. Direct frozen dependencies: [] (only Mathlib imports).
  escape_witness: private `curvature_unit_count`, the count-three conclusion
  for primitive integer curvatures satisfying the coefficient-3 equation.
  admission_basis: escape-witness.
- Four conditions of CLAUDE.md 3.2: (i) the main theorem explicitly applies
  curvature_unit_count; its elaborated proof is in the dependency closure;
  (ii) no frozen predecessor supplies this count, and the Mathlib finite-field
  power identity alone gives no count without the new Descartes divisibility
  argument; (iii) the curvature unit count is neither definitionally equal to
  nor a restatement of the radius valuation theorem; (iv) the resulting count
  is consumed to establish both the three-element valuation fiber and e>0,
  so it remains on the live derivation path after reduction.
- utility: none. All quantified radii are unbounded. The theorem is not bounded
  enumeration, a checker, a numerical reduction or a certified finite instance;
  the modular indicator is an application of the general finite-field theorem.
  Other utility fields: not-applicable(kind=none).
- New definitions `gcd4` and `sphereDescartes` state precisely common gcd and
  the rational coefficient-3 equation. All auxiliary lemmas remain private.
- Required project build, report production, Scribe checks and freeze still
  pending; a file check is not reported as `make lean` success.

## Project build and narrative

- `make lean` EXIT=0, measured 60.290 seconds on this macOS ARM worktree;
  12835 Lake jobs, target module built in 9.6 seconds. Baseline modules emitted
  replayed warnings; the target emitted only the standard three-axiom report.
  LEAN_CACHE: status=present, method=none, stamp_miss=null,
  project_olean_state=warm, mathlib_olean_state=warm, missing mathlib oleans=0.
  Full log and machine receipt are worker-owned files `lean.log` and `lean.json`
  in the supplied attempt directory. Local elapsed time is not a CI estimate.
- Added the canonical Scribe source and an attributed OEIS note. Library/Arith
  is already at 48 files; Library/ArithUnits did not exist, so the new note uses
  that registered domain (finite coprimality/residue structures). The note's
  Verified locator section contains the literal url and doi frontmatter lines.
  The mathematical proof is repo-derived, with OEIS acknowledged as the source
  of the conjecture. No existing proof is falsely attributed to the OEIS entry.
- `make lean-report` is in progress; Scribe compilation/emission and content
  checks remain pending. No generated Blueprint markdown has been hand-edited.

## Report, semantic echo and first emission

- `make lean-report` EXIT=0, 97.983 seconds. Canonical report:
  `.lake/build/stratalint/raw-lean-report.json`. It includes exactly one public
  authored theorem, primitive_sphere_radii_v3, statement_id
  `sha256:09c88b6e978ed31186462778333f69017d9fba0cba726bc6badb8e54518b1886`.
  All listed imports are Mathlib/Init, hence direct frozen prerequisites are [].
- The private curvature_unit_count statement_id is
  `sha256:ee17673c023abe39e40a70b2a2e726a9bd80a2883294a8fc904c03b59f990f52`.
- Worker-owned `SemanticEcho.lean` checked the exact requested target type,
  jointly verified all hypotheses for (1,3,3,3) and (12,12,39,52), and rejected
  (1,1,1,1) for the coefficient-3 equation. EXIT=0, 7.122 seconds. These are
  semantic probes only, not separately frozen instances or unbounded evidence.
  This does not rerun or re-certify the orchestrator's 49-solution enumeration.
- Lean's `ConstantInfo.value?.getUsedConstants` confirmed the direct elaborated
  edge primitive_sphere_radii_v3 -> private curvature_unit_count. This is a
  compiler semantic readout, not an inferred text-search dependency. The echo
  also reports only propext, Classical.choice and Quot.sound.
- First `make emit` EXIT=2, 19.447 seconds: the formula DSL rejected adjacent
  control word forall and identifier r (`\\forallr`). Added explicit Sp after
  all four quantifiers in the Scribe formula. The mathematical Lean source did
  not change. Emission after this repair is running; no claim of success yet.

## Emission and freeze receipts

- Repaired `make emit` EXIT=0, 61.459 seconds. Generated Blueprint mathematics
  was inspected; no generated Markdown was edited by hand.
- `make deposit-uncovered` EXIT=0, 96.897 seconds, with the exact starting base
  above and GID
  `D5/S3/Arith/Descartes/PrimitiveSphereRadii.primitive_sphere_radii_v3`.
  The canonical target ran report, header check, emission, and `ledger-align
  --add`; it returned `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED reason=NO_ATOM`.
- Module frozen statement_id:
  `sha256:fa7aaef171c6290060dd9d55c4c9c7025cf2ec5260ce11e2ad56e535970f4ac3`.
  Freeze event:
  `sha256:33b41a1e7d082e60b6a98003193f95e478a9028d1c125ef43d358aa93a6c8dfd`.
  The event records `prerequisite_frozen_node_ids: []`.
- No new theory source, ingestion atom, coverage edge, source-ledger rewrite,
  finite-instance freeze, sorry, private axiom or native_decide was introduced.

## Scribe content checks before PR

- Ran `bash tools/scripts/workflow/scribe-content-checks.sh
  .lake/build/stratalint/raw-lean-report.json ""
  462d0a4368ba5a890c5eab619c82437baa88966f` after emission and freeze.
  EXIT=0, 25.156 seconds; complete log and receipt are `scribe-content.log/json`
  in the worker attempt directory.
- `describe-report --check`: classified 10413 nodes, red=0. Existing open nodes
  and observations are reported by the tool; they are not claimed resolved here.
- Real KaTeX `markdown-check`: judged=1, formula(s)=1, red=0, covering the new
  generated Blueprint document. `projections --check` was not selected by the
  script because no projection JSON or producer implementation changed; it is
  not claimed as an independently executed check.
- Current delivery commits, including the no-atom freeze, have been pushed to
  `origin/lane/math/a390148`; PR creation is the next step.

## PR delivery and final scope

- Opened https://github.com/the-omega-institute/trureturing/pull/6739 against
  `dev` using `make pr-open HEAD=lane/math/a390148 MESSAGE=<attempt>/pr-message.md`.
  Creation succeeded and the canonical watcher observed OPEN with two required
  checks pending and one not yet reported. No CI success is inferred from that
  snapshot. Auto-merge was not requested.
- The only public theorem is the complete requested 3-adic result, with the
  original positive-radius, common-gcd and coefficient-3 rational hypotheses.
  There is no sorry or private axiom; the checked axiom closure is std3.
- Final unclaimed scope: no other prime clause, repetition formula, arbitrary
  chain, coefficient-2 circle result, global literature exhaustiveness, global
  priority, independent review/consensus, or merge. The user's numerical probe
  and triage remain attributed input. Pages not actually opened by this worker
  remain ASSUMED-UNVERIFIED, as specified in the search receipts.
- Runner-owned delivery contract: the worker publishes the full structured
  result and completion sentinel by temporary-file atomic rename in
  `/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/a390148-impl-0910/attempt-1`.
  Those files will contain the final commit, PR and actual CI status at completion.
