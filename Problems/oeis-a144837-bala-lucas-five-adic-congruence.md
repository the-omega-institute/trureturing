---
slug: oeis-a144837-bala-lucas-five-adic-congruence
bibkey: bala2022a144837
doi: null
url: https://oeis.org/A144837
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/BalaLucasFiveAdicCongruence
---

# Bala's Lucas recurrence and its growing five-adic congruence

## Problem

OEIS A144837, NAME (`%N`, verbatim):

> a(n) = Lucas(5^n).

Peter Bala's Nov 14 2022 recurrence (verbatim):

> a(n) = a(n-1)^5 + 5*a(n-1)^3 + 5*a(n-1) with a(1) = 11.

The settled FORMULA line (`%F`, verbatim):

> Conjecture: a(n+1) == a(n) (mod 5^(n+r+1)) for n >= r.

AUTHOR (`%A`, verbatim):

> _Artur Jasinski_, Sep 22 2008

The offset is `%O 1,1`. Both `n` and `r` range over the natural numbers
including zero, with the sole hypothesis `r <= n`. The sequence is
integer-valued and defined by Bala's recurrence, extended to zero with
`a(0)=1=Lucas(5^0)=Lucas(1)`. This gives `a(1)=11=A144837(1)` and agrees
with the OEIS domain `n >= 1`. Congruence means that the integer
`5^(n+r+1)` divides the integer difference `a(n+1)-a(n)`.

The exact Lean statement is:

```lean
theorem result (n r : ℕ) (hr : r ≤ n) :
    (5 : ℤ) ^ (n + r + 1) ∣ a (n + 1) - a n
```

Only the Conjecture line is settled for the recurrence interpretation,
covering every `n >= 1` and also `n=0`. The Lucas representation, the
5-adic limit (A269591), and A268922 are not claimed. The formal definition
does not use Lucas numbers.

## Motivation

The conjecture describes an unbounded family of growing divisors of
consecutive differences in a quintic recurrence. The expression
`a(n)^2+4` gains two powers of 5 at each step, explaining all the moduli
indexed by `r <= n` through one invariant.

## Gap

Readings of 2026-09-15: OEIS still marks the settled `%F` line
`Conjecture`; the entry was last edited 2026-07-28. OpenAlex returned
zero hits for `A144837`, the Math.SE API returned zero, and
formal-conjectures returned zero. The arXiv API gave no response, so
arXiv was not searched. These external readings are
`ASSUMED-UNVERIFIED` without independent online retrieval.

Repository prior art at the recorded `origin/dev = 66159474eb`:
`git grep A144837` returned zero hits. The immutable-commit search
`git grep -n A144837 66159474eb -- D5 Blueprint Library Problems` also
returns zero hits (exit 1). The frozen `BalaCubicThreeAdicCongruence`
is the 3-adic sibling with a different recurrence, seed, and invariant;
it does not instantiate to this target. Pinned Mathlib provides
`pow_dvd_pow`, `dvd_sub`, `mul_dvd_mul`, and `ring`; no Lucas(5^n)
sequence or this complete congruence was found in the searched scope.
The Mathlib pin is `db584cd6d46c92f209a44c0f1c829460d327499d`.
This is `not-found-in-searched-scope`, with no exhaustive literature or
priority claim. Bala's block proves only `mod 5^(n+1)` through the Gauss
congruences for Lucas numbers, and his 2026 note on strong divisibility
sequences concerns `a(n+k)-a(k)`. No literature proof of the
`5^(n+r+1)` strengthening was found in the searched surfaces.

Exact-integer checks give zero exceptions for `0 <= r <= n <= 8`
(45 pairs). On this range,
`v_5(a(n+1)-a(n)) = v_5(a(n)^2+4) = 2n+1`, so the modulus is sharp at
`r=n` for the tested indices. Here `v_5(x)` is the exponent of 5 in a
nonzero integer `x`; also `v_5(a(n)) = v_5(a(n)^2+1) = 0` throughout
this range. These are bounded observations, not universal exact
valuation conclusions.

Pre-registration issue #8117 (created 2026-09-15T15:07:22Z) precedes the first proof attempt (2026-09-15T15:08:31Z)

The problem is in the recent-small-conjecture tier. Historical openness
outside the listed search surfaces remains unverified.

## Route

1. Induction proves `5^(2n+1) ∣ a(n)^2+4`, beginning with `a(0)^2+4=5`.
   The proof uses the factored identities
   `a(n+1)^2+4 = (a(n)^4+3a(n)^2+1)^2(a(n)^2+4)` and
   `a(n)^4+3a(n)^2+1 = (a(n)^2+4)(a(n)^2-1)+5`.
   The induction hypothesis implies `5 ∣ a(n)^2+4`, hence the squared
   factor supplies two further powers of 5. Equivalently, writing
   `a(n)^2+4=5t` gives
   `a(n+1)^2+4 = 125t(1-10t+35t^2-50t^3+25t^4)`;
   the formal proof uses the two factored identities above.
2. The factorization
   `a(n+1)-a(n)=a(n)(a(n)^2+1)(a(n)^2+4)` transfers the invariant to
   divisibility of the difference by `5^(2n+1)`.
3. The bound `r <= n` gives `n+r+1 <= 2n+1`; exponent weakening by
   `pow_dvd_pow` and divisibility transitivity yield the conjecture.

The public theorem `result` has `proof_shape: content` and
`admission_basis: escape-witness`. The private theorem `a_sq_plus_four`
also has `proof_shape: content`. It is the escape witness, satisfying
the four §3.2 tests:

1. It occurs in the elaborated constant dependency closure of `result`,
   as a direct proof dependency.
2. Its unbounded growing-modulus invariant is established by arithmetic
   induction; no reviewed frozen or pinned upstream prerequisite gives
   it by instantiation, projection, or normalization. Divisibility and
   ring lemmas supply algebraic steps, not that induction conclusion.
   This classification is a semantic assessment of the searched scope.
3. The invariant about `a(n)^2+4` and exponent `2n+1` is neither
   definitionally equal to, an alias for, nor a restatement of the
   difference conclusion with its extra index `r`.
4. Its quotient `q` and equality are obtained by existential elimination
   and used in the actual divisor witness `a(n)(a(n)^2+1)q`. They remain
   on the live path after beta, zeta, and iota reduction; no dead term
   or discarded conjunction carries the invariant. Removing it leaves
   the growing-divisor obligation unproved by the reviewed prerequisites.

The public definition `a` has `proof_shape: definition` and is used by
`result`; the module's admission basis is `escape-witness`. There are no
direct frozen-project theorem dependencies. All other arithmetic steps
are local `have` terms or inline rewrites, with no companion declarations.

`question_answered` is exactly the displayed recurrence interpretation
of the Conjecture line, pre-registered in issue #8117.
`dominating_theorem_search: not-found-in-searched-scope` covers the
repository recurrence declarations and pinned Mathlib sequence,
divisibility, and iteration results. Generic iteration transports a
given invariant; it does not establish this arithmetic two-power gain.

`utility: none` applies to each declaration: `a` defines an unbounded
symbolic recurrence, `a_sq_plus_four` proves an unbounded invariant,
and `result` proves a universal congruence. None is bounded enumeration,
checker infrastructure, numeric reduction, or a certified finite
instance. The numeric experiment is not a formal premise. The remaining
computational utility fields are `not-applicable(kind=none)`.

## Falsifier

A natural pair `n,r` with `r <= n` and exact recurrence values for which
`(a(n+1)-a(n)) % 5^(n+r+1) != 0` would refute the conjecture.
At the boundary `n=r=0`, the difference is `11-1=10`, divisible by 5.

## Evidence

- `lake env lean D5/S1/Recurrence/BalaLucasFiveAdicCongruence.lean`:
  exit 0. The public surface is exactly `a` and `result`;
  `a_sq_plus_four` is private. The source contains no `sorry`,
  `native_decide`, or new axiom declaration.
- `tools/scripts/agent/header-check.sh` on the final module: exit 0;
  53 lines, 37 Lean files in the immediate directory, `generality: G`
  compliant. The seven-line header has a 76-character digest payload
  on a 90-character physical line.
- Scratch `#print axioms` audit of the final source: exit 0. The axiom
  closures are `[propext]` for `a`, and exactly `[propext, Quot.sound]`
  for both private `a_sq_plus_four` and public `result`. The elaborated
  proof directly depends on `a_sq_plus_four`, uses
  `Exists.casesOn` and `Exists.intro`, and the invariant uses `Nat.recAux`.
  The definitional-equality check of the invariant and result types
  returns `false`. The terms `example : ℕ := 0` and
  `example : (0 : ℕ) ≤ 0 := Nat.le_refl 0` also elaborate with exit 0.
- Deleting each direct import from an otherwise exact copy of the final
  module and running `lake env lean` gives:

  | Direct import | Deletion exit | Diagnostic |
  | --- | --- | --- |
  | `Mathlib.Algebra.Ring.Divisibility.Basic` | 1 | Unknown identifier `dvd_add` |
  | `Mathlib.Tactic.Ring` | 1 | Unknown tactics and unsolved goals |

  Both imports are necessary for the unchanged proof. Other used
  facilities arrive transitively through these two imports.
- `lake env lean -Dprofiler=true -Dtrace.profiler.threshold=1000` on the
  final module: exit 0. `/usr/bin/time -p` reports 6.16 seconds wall;
  Lean reports type checking 25.7 milliseconds and import 3.59 seconds.
  This is a warm-cache, single-file reading with Lean 4.33.0 on arm64
  macOS, of the module source whose frozen `statement_id` is
  `sha256:656ebad0b379b89c9562c8d11af66548cd7742ac1f9ae335b935f235725f55ba`.
- Exact-integer recurrence check: exit 0. It verifies the final source's
  defining clauses, computes through `a(9)` (1,355,942 bits), and checks
  all 45 pairs `0 <= r <= n <= 8` with zero exceptions. Values begin
  `1, 11, 167761, 132878596168524201724674011`. Both valuations in the
  Gap section are `[1,3,5,7,9,11,13,15,17]`; the next stronger modulus
  fails at each tested index. These finite data are not proof premises.

## Triage

`theorem`; resolution `proved` for the quoted Conjecture line, with
the integer recurrence and scope wall above.

## ASSUMED-UNVERIFIED

The OEIS quotations, attribution, edit date, external literature readings,
pre-registration chronology, and historical position of `origin/dev`
at `66159474eb` are readings dated 2026-09-15 without independent online
verification. The immutable-commit local search is separately checked
above. arXiv was not searched because its API gave no response.
Historical openness beyond the listed search surfaces and third-party
Lean ecosystem coverage remain unverified; no exhaustive search or
mathematical priority is claimed. There are no unproved mathematical
premises in the theorem. Independent semantic review, Scribe execution,
emitted Markdown fidelity, and repository admission are not established
by these single-file checks. The Lucas representation, 5-adic limit
(A269591), A268922, and unbounded exact valuations are not formal
conclusions here.
