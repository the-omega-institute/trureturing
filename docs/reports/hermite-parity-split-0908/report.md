# Hermite parity L1: partial Newton interface, blocked

Issue: https://github.com/the-omega-institute/trureturing/issues/6377

`verdict: blocked`. This is an implementation attempt for the coefficient-to-root-list
interface. Two consecutive Newton normalization failures triggered the prescribed stop.
The delivered module proves recursion uniqueness, compatibility with ring homomorphisms,
Vieta including the zero tail, and a root enumeration retaining multiplicities.
It does not yet identify recursive Newton sums with root power sums.

Provenance: one Codex implementation session; no local skill, delegated agent, or
independent review was used. Independent review: `ASSUMED-UNVERIFIED`.
Protected starting commit: `f1164377233bc771d6c477464e54a5941a22e253`.
Branch: `lane/math/hermite-parity-split-0908`.

## Calibration and type separation

`calibration_X6_minus_1`: independently recomputing the six roots of unity gives
`s_r = 6` when `6 | r`, and zero otherwise. The finite geometric sum proves this
directly: if `zeta^r != 1`, multiplying the sum by `1-zeta^r` gives zero; if
`zeta^r = 1`, every term equals one. The polynomial has simple roots since its
derivative `6 X^5` is nonzero at a sixth root of unity.

The moments from 0 through 10 are `[6,0,0,0,0,0,6,0,0,0,0]`. Therefore the
truncated matrix is `[[0,0,0],[0,0,0],[0,0,6]]`: diagonal entries are
`s_2=0`, `s_4=0`, `s_6=6`; the off-diagonal entries `s_3,s_4,s_5` are zero.
Its quadratic form is `6 v_2^2 >= 0`. For `f=X-X^5`, the complete form is
`s_2 - 2 s_6 + s_10 = -12`, and the root-count normalization gives `-12/6=-2`.
Also `(X-1)(X+1)(X^4+X^2+1)=X^6-1`, with the quartic strictly positive on
the real axis, so the only real roots are `1` and `-1`.

The single archived Lean probe `calibration.lean` proves truncated PSD and the
complete negative direction together, using the coefficient recurrence. It also
proves the real-root assertion. It passed `make lean` (EXIT 0, 23.60 s,
maximum RSS 3,292,725,248 bytes). Its equality to the frozen root-list moments
is **not** part of that kernel proof: the general bridge remains unproved.
The roots-of-unity calculation above and the exact Rational Ruby calculation
are independent checks, not a substitute for that bridge.

`type_separation`: `FullHermiteMatrix d A` and `TruncatedHankelMatrix d A`
are distinct structures, each with an explicit `entries` projection and no
coercion between them. They are distinct even with the same `d` and `A`.
The probe's `#check_failure` rejects a value of `FullHermiteMatrix 3 Real`
where `TruncatedHankelMatrix 3 Real` is required. This expected diagnostic
is not a proved conversion or a theorem containing `sorryAx`.
Complete entries use `s_(i+j)`; truncated entries use `s_(i+j+2)`.

## Lambda correction

`lambda_simplification`: the two supplied expressions are not equal.
For the falling factorial and `0 <= 2k <= n`, factorial cancellation gives

```text
(n)_k = n!/(n-k)!
choose(n,2k) (2k)! = n!/(n-2k)!
lambda = k! (n-2k)!/(n-k)! * (n+1-k)/(n+1).
```

Thus `(n-2k)!` belongs in the numerator. The ratio of the original expression
to the supplied second expression is `((n-2k)!)^2`.

| n | k | Original and corrected | Supplied second expression |
|---|---|---|---|
| 6 | 1 | 6/35 | 1/3360 |
| 4 | 0 | 1 | 1/576 |
| 8 | 2 | 7/135 | 7/77760 |

The first row is also checked by `norm_num` in the archived Lean probe.
The general factorial simplification is an algebraic derivation here, not a
delivered Lean theorem. General Lean verification: `ASSUMED-UNVERIFIED`.
This refutes that subformula; it does not refute the parity block identity.

## Newton interface and stopping readings

`newton_recursion`: `newtonSum d c` is defined by well-founded recursion with
zeroth value `d`. Coefficients are extended by zero past the degree using
`descendingCoeff`. The successor equation has the Newton endpoint term and
all interior terms, so the zero tail covers both ranges in the brief.
`newton_sum_unique` uses strong induction; `map_newton_sum` consumes it on
its live proof path to transport the sequence through an arbitrary ring homomorphism.

`descending_coeff_eq_root_esymm` applies pinned Mathlib Vieta and handles
the entire zero tail. `exists_root_enumeration` uses complex splitting,
`p.roots.toList.get`, and equality of the mapped multiset with `p.roots`.
Every repeated root is retained: no distinct-root set replaces the multiset.

The attempted consistency proof applied
`MvPolynomial.psum_eq_mul_esymm_sub_sum`, evaluated at the roots, and
reindexed the interior antidiagonal. Two consecutive normalization failures:

| Log | make lean EXIT | Seconds | Maximum RSS (bytes) | Remaining failure |
|---|---|---|---|---|
| newton-attempt-2.log | 2 | 13.21 | 3,194,683,392 | `simpa` did not identify the opposite-sign endpoint expressions |
| newton-normalization.log | 2 | 15.21 | 3,197,435,904 | `ring` left the cast/distributivity goal below |

```text
up(1+r) * E * (-1)^r = E * up(r) * (-1)^r + E * (-1)^r
E = (Finset.univ.val.map roots).esymm (1+r)
```

The unfinished source is archived as `newton-unfinished.lean`, including its
failed proof. It is not imported, deposited, or counted as a proof. In those
failed builds `newton_sum_eq_root_sum` depended on `sorryAx`; that declaration
was removed from the deliverable. No heartbeat, recursion-depth, or mathematical
constant was changed. The stopping rule ends this correspondence attempt.

`parity_block_identity`: unproved. No permutation matrix theorem, recursive
even/odd moment theorem, or connection to the frozen normalization was delivered.
No claim is made that this partial module is the requested complete calculator.

`scope_not_claimed`: this attempt does not prove FFC's `H0 >= 0` or `H1 >= 0`,
the nonnegative-root support criterion, odd-degree assembly, the convolution
coefficient formula, or the full Hermite parity block identity. It does not
replace algebraic squares by complex absolute squares. The PSD pair remains
the FFC target; no sign condition permits dropping `H1` in this delivery.

## Bind-only search and admission

`bind_only_attempt`: the first attempt imported the pinned Mathlib primitives
and the frozen Hermite criterion, tried direct search/simplification of the
all-orders coefficient-to-root-sum target, and did not close it. Complete probe
source is archived as `bind-only-probe.lean`. Its first whole build failed on
an unrelated unknown `#check` name; after removing that check, the probe itself
compiled during `newton-attempt-1.log`, while the candidate content module failed.
There is no successful bind-only proof of the requested target to return.
The executable initial guard tried `exact?` and `simp`; it did not explicitly
apply `sq_nonneg` or `linarith only` to the recursive identity or instantiate
the frozen PSD iff on that target. Consequently this is a limited failed
attempt, not verification that every allowed bind-only path is exhausted.
The archived calibration uses `linarith only` on its real-root factorization.

Collision check before implementation used
`git grep -n -i -P '(hermite.*parity|parity.*hermite|newton.*recurs|recurs.*newton)' -- D5`
(EXIT 1, zero hits). PCRE word-boundary positive control
`git grep -n -P '\bnewtonHankel_posSemidef_iff_roots_real\b' -- D5`
had three hits in the frozen criterion. A parity word-boundary control also
matched `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.lean`.
The analogous anchor search in `Meta/Digestion/backfill` had zero hits;
the criterion control found the covered 5040 atom. No matching anchor was
found in that searched scope. No claim of exhaustive ecosystem absence is made.

Pinned Mathlib v4.33.0 supplies Newton identities, Vieta, and complex splitting.
The frozen criterion uses `(sum_j roots_j^r).re / d` and a complete `Fin d`
matrix. The repository characteristic-polynomial reconstruction theorem does
not give the missing forward recursive interface. Loogle found the Newton
primitive (HTTP 200); anonymous GitHub code search returned HTTP 401, and
grep.app returned a security checkpoint. Those last two searches are incomplete.

`escape_witness`: `newton_sum_unique`, proved by strong induction at arbitrary
order. Its live consumer is `map_newton_sum`, with direction
`map_newton_sum -> newton_sum_unique`. This is the delivered escape claim,
subject to semantic review; the stronger planned root-sum consumer is unproved.
`admission_basis: escape-witness`. `proof_shape: content` for uniqueness and
its live ring-map consumer. Direct frozen prerequisites of this module: none;
its imports are Mathlib only. No independent proof-shape review is claimed.

The reindexing, zero/successor equations, Vieta, and root enumeration are
bind-only companions for issue #6377 L1. The recurrence equations are consumed
by uniqueness. The other companions have the pre-registered intended consumer
`newton_sum_eq_root_sum`; that consumer is archived and unproved, not an existing
closed declaration or coverage edge. The typed matrix constructors support
the archived joint calibration and the requested eventual parity theorem.
The archived root-sum theorem takes an enumeration as an argument. Enumeration
existence is for its intended specialization to every complex polynomial;
it is not a dependency of the archived proof body itself.

Per-public-theorem proof-shape accounting (direct frozen dependencies are `[]`
for every row; the module admission basis is `escape-witness`):

| Theorem | proof_shape | escape_witness or companion direction |
|---|---|---|
| newton_sum_unique | content | Its strong-induction construction; live in map_newton_sum |
| map_newton_sum | content | newton_sum_unique; map_newton_sum -> newton_sum_unique |
| newton_sum_zero | bind-only | newton_sum_unique -> newton_sum_zero |
| newton_sum_succ | bind-only | newton_sum_unique -> newton_sum_succ |
| newton_inner_antidiagonal_sum | bind-only | Intended newton_sum_eq_root_sum -> newton_inner_antidiagonal_sum |
| descending_coeff_eq_root_esymm | bind-only | Intended newton_sum_eq_root_sum -> descending_coeff_eq_root_esymm |
| exists_root_enumeration | bind-only | Intended newton_sum_eq_root_sum -> exists_root_enumeration |

Lean-generated structure eliminators, injectivity facts, and recurrence equations
only express those definitions; they introduce no separate computational claim.

`utility: none`, declaration by declaration:

| Declaration | Why outside all four computational utility classes |
|---|---|
| descendingCoeff | Arbitrary polynomial coefficient function; no certification claim |
| newtonSum | General recurrence; no certificate or bounded candidate search |
| newton_inner_antidiagonal_sum | Arbitrary finite-sum reindexing equality |
| newton_sum_zero | Defining initial value for arbitrary degree and ring |
| newton_sum_succ | Defining recurrence at arbitrary order |
| newton_sum_unique | Unbounded induction, not a fixed instance or numerical reduction |
| rootElementaryCoeff | General signed symmetric function; no checker |
| map_newton_sum | Arbitrary ring homomorphism compatibility; no numerical premise |
| descending_coeff_eq_root_esymm | General Vieta equality; no certified instance |
| exists_root_enumeration | Arbitrary-degree multiset enumeration existence, not bounded search |
| FullHermiteMatrix | General structure type; no certification operation |
| TruncatedHankelMatrix | Separate general structure type; no certification operation |
| fullHermiteFromMoments | General indexing construction; no positivity assertion |
| truncatedHankelFromMoments | General indexing construction; no positivity assertion |

## Validation and delivery

`axioms`: printed closures of uniqueness, ring transport, Vieta, enumeration,
and both calibration theorems are `[propext, Classical.choice, Quot.sound]`.
The finite calibration is outside the frozen module. `Trureturing.lean` was
not changed. `local_make_lean_EXIT: 0` for the delivered proof bodies and the
joint calibration; report/deposit/PR receipts will be recorded in the result envelope.
`make lean-report` also passed (EXIT 0, 71.78 s, maximum RSS 4,299,358,208 bytes),
and `make -C tools selftest` passed (EXIT 0, 7.62 s, maximum RSS 253,640,704 bytes).
The final header wording was re-inspected successfully (EXIT 0, 61.91 s,
maximum RSS 4,300,029,952 bytes). The first `make emit` failed because Scribe
has no automatic formula projection for these new declarations (EXIT 2,
8.21 s). The Scribe source now uses its supported `WithoutFormula()` path,
with declaration references and explicit narrative scope.

`make emit` then passed (EXIT 0, 62.43 s, maximum RSS 1,260,666,880 bytes).
It refreshed six unrelated mirrors already equal to current dev; those are
not part of this PR's authored changes. Before PR opening, the collision search
was repeated at dev `aee1eaff34f997e44f04147cee1010bb482c4c1b` with the same
zero-hit result and successful criterion/parity positive controls.

`frozen_output: frozen, uncovered`. The exact workflow was

```text
make deposit ATOM_ID=uncovered-hermite-parity-split-0908 \
  GID=D5/S3/Constants/Moments/CoefficientNewtonSums.map_newton_sum \
  BASE=f1164377233bc771d6c477464e54a5941a22e253
```

`uncovered-hermite-parity-split-0908` is an explicitly unmatched workflow
argument, not a claimed atom. The header precheck passed; ledger alignment
reported `added=1, conflicts=0`; coverage then returned `COVER_INVALID` because
that identifier is absent. The workflow emitted
`PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED` and exited 2 (94.93 s, maximum RSS
1,486,454,784 bytes). No coverage edge was fabricated.

State: `Golden/Frozen/state/D5/S3/Constants/Moments/CoefficientNewtonSums.lean.json`.
Statement identity: `sha256:2eaa9526bade862a1a821b87daf78426f82845dc681d9a7dc8f637cb255c66c6`.
Freeze event: `sha256:98abbda2bcb7f6fd8bd002784480a485d613306472ca3e3ed70378ace72da202`.
Its recorded frozen prerequisites are `[]`.

`pushed`: implementation commits `877ff6375d` and `c42193988f` were pushed;
the final push SHA and PR/check status are recorded in the completion envelope.
`pr`: https://github.com/the-omega-institute/trureturing/pull/6406, opened with
`make pr-open`, without auto-merge. The first run passed engineering and Lean
checks but failed SL-003: the merge candidate had 25 files in `docs/reports`,
above the admission limit 24. This report was moved into its own subdirectory;
the frozen Lean source, state pin, and event were not changed. SL-022's Scribe
protected-surface message is informational; its rule passed locally and in CI.
The final required-check receipt is in the completion envelope.

The full local `make preflight` at `ef50aedbad` passed before that path move:
EXIT 0, 796.04 s, maximum RSS 6,653,181,952 bytes. All seven test projects
passed, totaling 4,878 tests. The candidate's admission gate also passed.
This local pass used the starting baseline; it did not detect the additional
report in CI's newer baseline `6e81408402e2a5fdbb980129770f149ad07ea00d`.
`assumed_unverified`: the unproved root-sum correspondence, frozen normalization
bridge, parity identity, general Lean factorial simplification, and independent
semantic review are `ASSUMED-UNVERIFIED`.

Worker artifacts and detailed logs reside at
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/hermite-parity-0908/attempt-1`.
The final `result.json` in that directory is the completion receipt.
