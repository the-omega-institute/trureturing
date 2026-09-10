# Finite-prime smooth Robin attempt (2026-09-09)

Provenance: no skill invoked; Codex implementation worker, one source of
judgment, no independent review or consensus claimed. The caller supplied the
consensus-rnd/sshx implementation artifact contract. LANE #6160. User scope:
bind-only first, stop on success, no deposit/cover/freeze, PR without auto-merge.

## Outcome

**Bind-only; user stop rule 1 triggered. No D5 module is delivered.**
Run 03 of `make lean` exited 0 (12743 jobs). The unrestricted-P theorem,
the positive logarithm-domain check, and the seven-smooth tail specialization
all pass with exactly `[propext, Classical.choice, Quot.sound]`.
The ten named theorems are retained, with identical checked bytes, in
`docs/reports/robin-smooth-general-0909-snippets.lean`, outside the build glob.
Its temporary build location was `D5/S3/Arith/Robin/FinitePrimeProbe0909.lean`.
SHA-256: `372ad2da2dfe7d969966211569ca943c4a5fc43ebdb9953ecd0afa954b9e655d`.
No production Lean, Scribe, frozen state, or digestion file is changed.

The exact checked target is:

```lean
theorem RobinSmoothProbe0909.robin_smooth
    (P : Finset Nat) (hP : forall p, p ∈ P -> p.Prime)
    (n : Nat) (hn : 0 < n) (hs : forall p, p.Prime -> p ∣ n -> p ∈ P)
    (ht : P.prod (fun p => (p : Real) / ((p : Real) - 1)) /
      Real.exp Real.eulerMascheroniConstant < Real.log (Real.log (n : Real))) :
    (ArithmeticFunction.sigma 1 n : Real) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real))
```

`Finset.prod` is the same product as the proposed big-operator notation.
There are no added hypotheses. The theorem derives exp(1)<n from ht and hn;
thus both logarithms and the denominator are on their intended positive
domain on every admissible input. No bounded enumeration occurs in the proof.

Proof shape: bind-only. Escape witness: null. Admission basis:
`not-applicable(user-stop-rule-1; report-only)`. None of the three module
admission routes is invoked, because the user explicitly requires stopping
without a module on a successful restricted reproof. No exception is claimed.

## Declaration Accounting

These are archived probe declarations, not new public D5 API. All have
proof_shape=bind-only, escape_witness=null, and no requested admission.

| Declaration (RobinSmoothProbe0909 prefix) | Binding source or consumer edge |
| --- | --- |
| prime_factor_gt_one | prime.one_lt; division-order rewrite; linarith only |
| local_ratio_lt | geom_sum_eq; sub_lt_self; positive-division monotonicity |
| sigma_ratio_product | Mathlib sigma factorization and natural prime factorization; cast/product rewrites |
| support_product_le | Finset.prod_le_prod_of_subset_of_one_le; prime-divisor membership projection |
| sigma_ratio_lt | Finset.prod_lt_prod_of_nonempty; local_ratio_lt; support_product_le |
| threshold_domain | product positivity, log_pos_iff and lt_log_iff_exp_lt |
| robin_smooth | sigma_ratio_lt and threshold_domain; positive-division rewrite |
| empty_support_excluded | primeFactors_eq_empty; empty membership; n nonzero |
| seven_tail_threshold | frozen rational log/gamma bounds plus exp lower sum and monotonicity |
| robin_seven_smooth_tail | robin_smooth at P={2,3,5,7}; seven_tail_threshold |

The main theorem and general algebra/order helpers have utility kind none:
they prove universal statements, not an enumerator, checker, numeric reduction,
or isolated certified input. The tail threshold is a report-only numerical
side-condition check; it is not submitted as a public finite certificate.
The anonymous n=1/P=empty equality is also a report-only diagnostic. Neither
is used to obtain module admission. The tail consumer quantifies over all
four exponents and is a direct companion specialization, not an enumerated set.

Direct frozen dependencies of the main theorem and its helpers: none, only
pinned Mathlib. The report-only `seven_tail_threshold` uses
`D5/S3/Arith/GoldenResource/RobinRationalBasis.eulerMascheroni_decimal_bounds`
and `.log_pow_two_mul_bounds`, with the public `atanhPartial` definition;
module statement_id
`sha256:6dcafd483a23c78180a3518807013e46c0dccfcb211d2d5f442207eb1ee621c2`.
Scope: the stated rational gamma bracket and the dyadic logarithm bracket for
k>=1 and 1<=y<2. No private SevenSmooth helper or enumeration is referenced.

## Seven-Smooth Instantiation

The checked `RobinSmoothProbe0909.robin_seven_smooth_tail` has exactly the
SevenSmooth conclusion and hypothesis `131072 <= 2^a * 3^b * 5^c * 7^d`.
In particular it covers the requested strict n>131072 segment (and its endpoint).
Its proof starts `apply robin_smooth {2, 3, 5, 7}` and supplies:

- primality of 2,3,5,7;
- positivity from n>=131072;
- prime support by `Nat.Prime.dvd_mul` and `Nat.prime_eq_prime_of_dvd_pow`;
- C(P)=35/8, normalized by norm_num, and `seven_tail_threshold hn`.

The threshold proof derives exp(gamma)>89/50 and loglog(n)>123/50 from the
frozen public rational bounds and monotonicity. Since
(89/50)*(123/50)=10947/2500>35/8, the strict threshold follows.
All three numeric quantities are certified in Lean, independently of the
floating-point witnesses. Frozen `SevenSmooth.lean` is untouched; its
5040<n<131072 part is neither generalized nor reimplemented here.

## Reproduction And Limits

Place the archived snippet's unchanged bytes at its temporary D5 path above,
run `make lean`, and remove that temporary source afterwards. Do not register
or freeze it. Run the Node witness script for the separate numerical diagnostic.
Run 03 retained one harmless tactic-style warning in the tail instantiation;
this is a successful build, not a warning-free claim. No budget was changed.

No mathematical novelty, independent review, exhaustive third-party search,
full Robin theorem, RH consequence, common 5040 threshold for arbitrary P,
or rational enclosure of T is claimed. CI and PR status are separate from
the local kernel verification; this delivery requests no merge or auto-merge.

Final-tree `make lean-report` exited 0. The canonical raw report uses schema
`stratalint-raw-lean-report-v2`; producer report SHA-256 is
`de9a643467ce79509b2cda46ca6fa93524184d6dc221484166fd1f20d701d76b`.
The archived probe is outside that report's current D5 source set.
`git diff --check` exited 0. `git merge-tree --write-tree HEAD origin/dev`
exited 0 against `9e1687db6cb75fed0c3da3a48a9574ec4b07c723`, producing union
tree `9a173d1dfca2bda2dcd962de1e232265fe5bf383` with no conflicts.

PR: https://github.com/the-omega-institute/trureturing/pull/6574 (base dev).
At creation it was OPEN, with autoMergeRequest=null. The canonical pr-open
command waits for required CI; its eventual exit and check outcomes are
recorded in the worker-owned result.json, not inferred from the local build.

## Preregistered Scope

Baseline: `1faf06c8bf58b7221f4cd8b35210705064761e4e`, equal to the local
`origin/dev` at the first reading. Working branch:
`lane/math/robin-smooth-general-0909`. The initial tree was clean.
Read both tracked brief notes and all 764 lines of `CLAUDE.md`, then
`agents/CONTEXT.md`. There is no ATOM_ID in this task; the note's show-atom
instruction therefore has no supplied atom to resolve. The user statement is
the mathematical target, not the topic of the worktree's older name.

Target: for every finite set P of natural primes, every positive n whose prime
divisors belong to P, and C(P) = product over P of p/(p-1), prove
C(P)/exp(gamma) < log(log(n)) implies sigma_1(n)/n < exp(gamma)*log(log(n)).
No restriction on the number of primes or their exponents is permitted.

First attempt: only pinned Mathlib instantiation, frozen public projections,
and normalization, including `sq_nonneg` and `linarith only` if needed.
Success triggers user stop rule 1: report bind-only and retain no D5 module.
Other preregistered stops: enumeration proved necessary, an actual
above-threshold Robin counterexample, or weakening P to force compilation.

If direct binding fails, the proposed candidate escape is the strict
prime-support product estimate obtained from sigma multiplicativity and the
geometric remainder. It is not presumed to be content: Mathlib product-order
and geometric-sum facts must first be tested as a complete binding proof.

## First Search Receipt

Pinned Lean and Mathlib: v4.33.0; Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` (lake-manifest.json).
`git ls-tree origin/dev --name-only D5/S3/` confirms the existing Arith domain.
Read all three existing Robin modules: SevenSmooth, PaddingRatio, PaddingTailMass.
Also read GronwallUpperEnvelope and inspected the objective-factorization,
GronwallLowerEnvelope, RobinExponentSwap, and RobinRationalBasis candidates.

Repository searches (literal candidates, not semantic absence proofs):

- `rg -l 'ArithmeticFunction\.sigma|robin_|reciprocalGeomSum' D5 -g '*.lean'`
  returned 14 files, including Gronwall upper/lower envelopes and SevenSmooth.
- `rg -n '\b(sigma|robin|Robin)\b' D5/S3/Arith/Robin/SevenSmooth.lean --stats`
  returned 17 matches on 17 lines. This positive control exercises the same
  word-boundary and alternation features as the broader search.
- Searching sigma/prod/lt/le combinations in pinned Mathlib NumberTheory hit
  its multiplicative factorization and the crude sigma_le_pow_succ bound;
  no exact finite-prime Robin theorem was found in that searched scope.
- Online Loogle query `ArithmeticFunction.sigma` succeeded and returned 31
  declarations. Search capability is available. This online index is not a
  substitute for checking the pinned source and elaborating against it.

Pinned Mathlib hits, to reuse rather than reprove:

- `ArithmeticFunction.isMultiplicative_sigma` and
  `ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`
  (ArithmeticFunction/Misc.lean:202,206).
- `ArithmeticFunction.sigma_one_apply_prime_pow` (same file:171).
- `Nat.prod_primeFactors_pow_factorization` (Factorization/Basic.lean:483).
- `Nat.mem_primeFactors`, `Nat.nonempty_primeFactors` (PrimeFin.lean:41,90).
- `geom_sum_eq` (Algebra/Field/GeomSum.lean:43).
- `Finset.prod_le_prod`, `Finset.prod_lt_prod_of_nonempty`, and
  `Finset.prod_le_prod_of_subset_of_one_le` (ordered big operators).
- `geom_sum_lt` was found but is in the canonically ordered semifield section:
  it does not directly instantiate at Real. The field formula plus order
  normalization remains an available binding route.

Frozen interface actually read:
`D5/S3/Arith/Robin/SevenSmooth.robin_seven_smooth`, module statement_id
`sha256:fbe79d554d7a04b6283b456ed63a4042bc51a9414cad8429ee3b7803189b1a52`.
Scope: products of powers of 2,3,5,7 above 5040. Its auxiliary product bound
and logarithmic certificates are private, so they are not frozen public
projections available to the general theorem. GronwallUpperEnvelope.sigma_split
has an additional exponential error and an initial-prime-segment product;
its public statement is not the requested arbitrary-P estimate.

## Degenerate Points: Initial Check

- At n=1 and P empty, sigma_1(n)/n = 1 = C(P). Thus the brief's auxiliary
  strict bound, read without a nondegeneracy condition, is false. This is not
  a counterexample to the main implication: C(P)/exp(gamma)>0 while Lean's
  log(log(1))=log(0)=0, so its threshold premise fails.
- For n>1 the prime-factor set is nonempty. Each prime-power ratio is strictly
  below p/(p-1); multiplying over the nonempty support preserves strictness.
- A prime in P outside the support contributes p/(p-1)>1, so enlarging the
  support product to P raises the bound, not lowers it.
- For positive natural n at most e, n is 1 or 2. At n=1 the totalized loglog
  is zero; at n=2 it is negative. The positive threshold excludes both.
  The probe will formally derive n>e from the original hypotheses instead of
  silently adding it as a stronger assumption.
- P empty and n positive and smooth forces n=1, again excluded by the threshold.

## Historical Initial Status

No target Lean proof has yet been checked. No production declaration, new
module, admission basis, or escape witness is claimed. Numerical witnesses,
the seven-smooth tail instantiation, and axiom checks are pending. No exhaustive
search, mathematical novelty, or implication concerning RH is claimed.
Independent review and pages not actually opened are unverified.

## Bind-Only Stop Observed

Run 01: `make lean` exited 2. The exact unrestricted-P main theorem
`RobinSmoothProbe0909.robin_smooth` and its six live prerequisite helpers
elaborated successfully with only `[propext, Classical.choice, Quot.sound]`.
The separate empty-support diagnostic failed because an indented term was
parsed outside its lambda; its error-recovery `sorryAx` is not proof evidence.
The main theorem's closure does not contain this failed diagnostic.
The repair is confined to the diagnostic, with no hypothesis changes.

The user stop rule is now triggered: **bind-only**, no production module.
Remaining work is artifact validation and the specifically requested
seven-smooth-tail instantiation report. No content implementation proceeds.
The successful estimate uses `geom_sum_eq`, `sub_lt_self`, positivity,
division-order equivalences and finite product-order theorems; it does not
need `sq_nonneg`, nonlinear arithmetic, enumeration, induction, or new
analytic input. The sigma multiplicativity/factorization is Mathlib's own.
`threshold_domain` derives exp(1)<n from exactly the original threshold and
positivity assumptions, and is used by the main proof.

Run log: runner attempt directory, `lean-bind-01.log`.
Cache receipt: status=present, method=none, stamp_miss=null,
mathlib_olean_state=warm, project_olean_state=warm.

Run 02: `make lean` exited 2. The repaired empty-support diagnostic and the
seven-tail threshold now both pass with the standard three axioms. The tail
consumer failed only on concrete primality goals left by `norm_num` and on
the unevaluated rational product of the four Euler factors. Use `decide` for
the four fixed primality facts and `norm_num` for the product; no domain,
bound, or proof budget changes. `lean-bind-02.log` records the full failures.

Incidental command accounting: querying the nonexistent optional
Evidence/D5/S3/Arith/Robin directory exited 1; searching for nested AGENTS.md or
CLAUDE.md in D5/Blueprint/Evidence/tools returned 0 matches (rg exit 1).
Neither is treated as evidence that a theorem is absent.

## Numerical Witnesses

`node docs/reports/robin-smooth-general-0909-witnesses.mjs` exited 0.
Integers and sigma values use exact BigInt prime-power formulas; logarithms,
gamma and exponentials are explicitly IEEE-754 diagnostics, not interval or
Lean certificates. These are specified witnesses, not enumeration of a range.

| P | n | sigma(n) | C(P)/exp(gamma) | loglog(n) | sigma(n)/n | Robin RHS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| {2,3} | 1024 | 2047 | 1.6843784507006554 | 1.9360721724123813 | 1.9990234375 | 3.4482847455220553 |
| {2,3,5,7} | 262144 | 524287 | 2.4563852406051225 | 2.5238588373145 | 1.9999961853027344 | 4.495175362041667 |
| {2,3,5,7} | 5040 | 19344 | 2.4563852406051225 | 2.1430219509746613 | 3.8380952380952382 | 3.8168772880285116 |
| empty | 1 | 1 | 0.5614594835668851 | 0 (Lean totalization) | 1 | 0 |
| {2} | 2 | 3 | 1.1229189671337703 | -0.36651292058166435 | 1.5 | -0.6527860536850343 |

The first witness includes the unused prime 3 and satisfies every premise and
the conclusion. The second is in the seven-smooth tail. The third satisfies
positivity, n>e, primality, and smoothness; only the threshold premise fails,
and the Robin conclusion is false. This supplies the required two-sided check.
For P={2,3,5,7}, the computed T is 116143.04312771709; no new rational enclosure
is claimed. The temporary unrestricted-P Lean probe is currently compiling.

Run 03 supersedes the pending/failure states above: `make lean` exited 0;
all ten named declarations print exactly the standard three axioms. The
snippet was archived with no proof-byte changes, and the temporary D5 source
was removed. No enumeration of smooth integers or admitted finite instance
was introduced. The earlier failed build exits remain part of the record.
