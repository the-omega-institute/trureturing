# Robin inequality for the entire 7-smooth family

Provenance: no skill; one Codex implementation worker, direct execution and
self-checks; no independent review or multi-model consensus claimed.
LANE: #6160. Baseline: a8809894ea0f1dac06913ed56e09db6223d7ddfa.
Branch: lane/math/robin7smooth-0909.
Atom: c3316916b643d8cf28de3e1b451f7f3ba61d1337f85a87b7eb42cc1568f9621f.

## Preregistered task and stops

First attempt: pinned Mathlib instantiation, frozen projections and normalized
rewriting only (including sq_nonneg and linarith only). Success means bind-only
and immediate stop without a new module.
Otherwise measure the threshold and the finite 7-smooth interval before writing
a proof. More than 5,000 interval members means blocked-on-cost. A counterexample
means immediate stop and report. The intended target quantifies over all four
natural exponents, with product strictly greater than 5040; a single certificate
does not discharge it. The initial atom-read failure was resolved below.

Proposed escape witness, conditional on a failed bind-only attempt: a uniform
strict divisor-sum bound for all products of powers of 2, 3, 5, 7, combined with
a certified analytic tail and private handling of the measured finite interval.
No public positive bounded-enumeration declaration is planned.
No deposit, cover, freezing, budget changes, new domain, or auto-merge authorized.

## Initial evidence

- Read tools/scripts/agent/probe-brief-note.txt first, then all of CLAUDE.md,
  agents/CONTEXT.md and tools/scripts/agent/deposit-brief-note.txt.
- git status --short --branch: clean; branch tracks origin/dev.
- make show-atom ATOM_ID=<full atom>: exit 2, CLI executable absent in this tree.
- make -C tools build: exit 2, no such target. Correct canonical target is dotnet.
- make -C tools dotnet: exit 0, zero warnings/errors.
- Canonical show-atom retry: exit 0; coverage_gids=[]; the raw text states
  sigma(n)/n < exp(gamma_E) log log n for n=2^a 3^b 5^c 7^d>5040,
  and explicitly permits arbitrarily large exponents. No brief/body discrepancy.
- make lean-cache-ensure: exit 0, seeded by clonefile from the main checkout,
  project and Mathlib states warm; no bare lake invocation.

## Library searches and the first proof attempt

Pinned Lean v4.33.0; Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Read RobinRationalBasis.lean in full and its frozen state:
D5/S3/Arith/GoldenResource/RobinRationalBasis,
statement_id sha256:6dcafd483a23c78180a3518807013e46c0dccfcb211d2d5f442207eb1ee621c2.
Its robin_delta_10080_pos applies only to 10080; robinPositiveJudge_sound
requires a certificate and analytic brackets for the same individual n.

Search receipts (textual candidate discovery, not exhaustive semantic claims):

- rg -n '\b(robin|Robin|robinDelta|RobinPositiveJudge)\w*\b|7.smooth'
  D5 --glob '*.lean' --glob '!SevenSmoothBindProbe.lean': 112 matching lines.
- Same word-boundary/alternation features, positive control:
  rg -n '\b(robin_delta_10080_pos|robinPositiveJudge_sound)\b'
  D5/S3/Arith/GoldenResource/RobinRationalBasis.lean: 6 matching lines.
- rg -n '\b(robin|Robin)\w*\b|7.smooth'
  .lake/packages/mathlib/Mathlib/NumberTheory --glob '*.lean': 0, exit 1.
  Whole Mathlib matches include author names; they are not Robin inequalities.
- Mathlib positive control with the same word boundaries found
  sigma_one_apply_prime_pow, isMultiplicative_sigma and Euler constant bounds.
- gh search code '5040 sigma language:Lean' --limit 50: six files. Opened
  project-numina/LeanTriathlon at 2aede4209c203ae9901eff870744e4b77dc6173f,
  LiveLeanTriathlonSorry/RobinTheorem/All.lean: RH equivalence ends in sorry.
  Opened the other number-theory candidate, open_problems at
  ae68b78aab261523b3c6af2c415d39a3501b9a8e,
  math/riemann_hypothesis/lean/CertificateEquivalence.lean: Robin is an axiom.
  Neither supplies an admissible proof. Other four search hits not opened.
- gh search code '"smooth" "5040" language:Lean' --limit 30: one algebraic
  geometry path, not opened. Search service is available; completeness unclaimed.

A temporary example-only Lean probe was run through make lean. It attempted
direct single-point reuse, normalization and linarith only with sq_nonneg,
then attempts the frozen checker at the universal product. No public theorem
or admitted proof was introduced. The probe was removed after reading
the actual diagnostics. Its log is attempt-1/bind-only-build.log.

Result: exit 2, required target SevenSmoothBindProbe failed. The restricted
linarith attempt failed to contradict robinDelta(product) <= 0. The frozen
10080 log-log bracket has the wrong argument for the universal product.
The single-instance checker application also hit the default recursion limit;
no budget was changed. This is a failed bind-only attempt, not a proof that
every possible bind-only proof is impossible. No RH premise is available or used.

## Threshold and enumeration measurement

measure.py uses fractions.Fraction throughout the decisions, with the geometric
atanh remainder and exponential Taylor tail. Decimal fields are display only.
The frozen Euler bracket implies that the crossing T, defined by
exp(gamma) * log(log(T)) = 35/8, lies strictly between 116141 and 116144.
The selected exact tail start is 131072 = 2^17; its certified rational lower
bound for the right side displays as 4.393371363221533 > 35/8.

The exponent box is 0..16, 0..10, 0..7, 0..6 (10,472 tuples), of which exactly
482 distinct products satisfy 5040 < n < 131072. First: 5103=(0,6,0,1).
Last: 129654=(1,3,0,4). An independent direct integer loop gave the same count.
All 482 pass the exact-rational exploratory comparison; no counterexample or
uncertified case. Minimum certified normalized margin displays as
0.05610237980934384 at 10080, sigma=39312. This is not yet a Lean proof.
The initial diagnostic windows excluded their endpoints; four smooth endpoints
(10000,20000,40000,80000) were in the total 482 but omitted from window counts.
The diagnostic window filter has been corrected to include lower endpoints.

Preregistration v2, before implementation of the public theorem: the concrete
escape witness will be a private finite arithmetic clearance, small_values,
bounding sigma/n by 381/100 below 10000, 197/50 below 20000, and 407/100 below
131072. These new integer inequalities are on the live path of the full theorem,
are not supplied by frozen predecessors, and are not definitionally equivalent
to a Robin inequality (they contain no log, exp or Euler constant). The generic
factorization bound may itself be bind-only after inlining; it is not claimed
as the escape witness. Only the unrestricted final theorem will be public.

Strictness: each finite prime-power factor is strictly below p/(p-1).
The product over actual prime support is strictly bounded when the support is
nonempty, which follows here from n>5040>1. The fixed four-factor product also
handles exponent zero: that factor equals 1 and remains strictly below p/(p-1).
Log(log x) is strictly increasing for x>1 because log x>0; therefore all lower
thresholds transfer in the forward direction. No reversed inequality is used.

## Universal implementation

The complete theorem is now proved in D5/S3/Arith/Robin/SevenSmooth.lean:
D5.S3.Arith.Robin.SevenSmooth.robin_seven_smooth. Its four natural exponents
have no upper bounds, and its only hypothesis is that their product exceeds
5040. The conclusion is the atom's strict sigma(n)/n Robin inequality.

The first implementation build exited 2 on integration typing mistakes. The
second make lean exited 0 (12735 jobs; new module 11 seconds). The finite
arithmetic and analytic bounds passed at the unchanged default budgets.
The printed axiom closure is exactly propext, Classical.choice, Quot.sound.
Logs: attempt-1/implementation-build-1.log and implementation-build-2.log.
An unused tactic warning in the second build was removed before final checks.
The subsequent make lean also exited 0 (12735 jobs; new module 11 seconds),
with no warning from SevenSmooth and the same standard axiom closure; log:
attempt-1/implementation-build-final.log.

All helper definitions and theorems are private. The finite proof uses
fin_cases and decide +kernel on the exponent box. Its three branches contain
71, 89 and 322 actual smooth numbers, respectively. Beyond 131072 the strict
35/8 divisor-sum bound and monotone log-log lower bound cover every exponent.
The tail's simpler Lean rational certificate is
(89/50)*(123/50) = 10947/2500 > 35/8; it does not rely on the displayed decimal
crossing estimate or on the Python experiment.

Per public declaration (only robin_seven_smooth): proof_shape=content;
admission_basis=escape-witness; utility=none. The preregistered private
small_values is in the dependency closure (the live hv fact), supplies new
integer inequalities absent from the frozen predecessors, is not definitionally
equivalent to the Robin conclusion (no exp/log/gamma), and is consumed in all
three finite branches. The general geometric estimate is not claimed as the
escape witness. These are author assessments, not machine classification.

## Report, Scribe and two-sided nonvacuity

make lean-report exited 0. Report input address:
sha256:a114c4f0ad995a4b56671ca81dde48afae05b615f262c7ed94b750533782d074.
Raw report SHA-256:
b6d8d996cfef7088928232d5170f0354d0a4f624b1c83f0e6788863b88885fea.
The new source is bound by
sha256:650a2ef0a93531eb21bff7133b8ab4587c02bc5e3ab4a2a46717ccebc2394a5d.
The sole public included declaration has statement_id
sha256:f22c3edbec1a3d227094dd2e2884f48ca1fd14c62a89fad16111d41fbfe5b15b
and exactly the three standard axioms. The raw report also includes 15 private
source declarations; inclusion in the identity report does not make them public.

make emit exited 0 and generated the corresponding SevenSmooth.md from the
Scribe definition. The only theorem node uses StatementSource.FromAuthor with
a typed formula quantifying all four natural exponents and the strict bound.
The generated document was read and matched to the Lean statement.

The updated exact-rational experiment exited 0 and gives both nonvacuity sides:

- Positive: n=10080=2^5*3^2*5*7, sigma=39312, sigma/n=39/10.
  The Robin right side lies in
  [395610237/100000000, 98902619/25000000], strictly above 39/10.
- Outside the hypothesis: n=5040=2^4*3^2*5*7, sigma=19344,
  sigma/n=403/105. The Robin right side lies in
  [76337533/20000000, 76337579/20000000], strictly below 403/105.
  This is not a counterexample to the theorem, since n>5040 fails.

These brackets are outward-rounded rational enclosures, and all comparisons
are exact. They are diagnostic evidence, not additional public finite theorems.
The measured finite count remains 482; corrected five-window counts are
71, 89, 103, 121, 98. Logs are attempt-1/lean-report.log, emit.log and
measurement.json. git diff --check exited 0.

## Local admission and current-base check

make -C tools selftest exited 0 (SELFTEST PASS; deterministic output comparison).
The raw CLI check against immutable fork baseline
a8809894ea0f1dac06913ed56e09db6223d7ddfa exited 3, with all content checks
passed and one SL-022 protected-surface diagnostic for the new Scribe source.
Its exact final marker was PROTECTED_SURFACE_CHANGE count=1; this is not an
exit-zero claim. Scribe verification passed. SL-031 observed utility kind=none,
explicitly semantics=unverified-by-machine. SL-034 observed the intentionally
absent frozen state. The CI workflow at .github/workflows/ci.yml:706-713 accepts
0 or 3 after the complete candidate content check; PR CI remains authoritative.
Logs: attempt-1/selftest.log and admission-local.log.

Current dev at the final pre-PR lookup is
6ba4ff1193eac1fe21a54b6ec688cd3cfc75b3aa. git merge-tree --write-tree --messages
against candidate 2bfa101e79d778d39e6965d4b651fbe33c0cb155 exited 0 without
conflicts (result tree 62f094dd8b1179bf82c90b9f2865fa947c119984). No files were
deleted between the fork baseline and that dev revision, so the intersection
with retired paths is empty. The PR diff contains exactly five added files.

The current-dev duplicate query used git grep -n -P
'\b(robin|Robin|robinDelta|RobinPositiveJudge)\w*\b|7.smooth' <dev-sha> -- D5
and returned 112 matching lines. The positive control with the same word-boundary
and alternation features, '\b(robin_delta_10080_pos|robinPositiveJudge_sound)\b',
returned six. No newly dominating full-family result appeared in that scope.

## Current nonclaims

No claim of mathematical novelty, exhaustive library/web search, a Lean proof
of the exact crossing interval or the count 482, independent review, machine
validation of proof_shape, or implication to/from RH. The family theorem itself
is kernel-checked; count and crossing diagnostics use exact rational experiments.
The unopened external search hits remain ASSUMED-UNVERIFIED. No deposit, cover,
freeze, merge, or final admission has occurred.
