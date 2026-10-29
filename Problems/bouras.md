---
slug: bouras
bibkey: bouras2023continuedfractionmultiplicity
doi: null
url: https://oeis.org/A363347
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity
---

# Prime multiplicities in Bouras's continued fractions

## Problem

M. Bouras, OEIS A363347, COMMENTS, Conjecture 3:

> Conjecture 3: Except for 5, the primes all appear exactly twice.

M. Bouras, OEIS A363102, COMMENTS, Conjecture 2:

> Conjecture 2: All prime numbers appear either twice (same as A356247 and A357127) or three times.

For $n\ge3$, let $K(n,x)$ be the reciprocal of the right-folded fraction
$2-3/(3-4/(\cdots- n/x))$. Define
$a_4(n)=\operatorname{den}(K(n,-4))$ and
$a_2(n)=\operatorname{den}(K(n,-2))$, using the positive reduced rational denominator.
The first claim counts exactly two indices for every occurring prime $p\ne5$;
the second counts exactly two or three for every occurring prime $p$.
This dossier anchors A363347 Conjecture 3; the sibling settlement has its own
[dossier](bouras-a363102.md). Neither statement asserts that every prime occurs. This is the binding reading
in preregistrations #18626 and #18627, both tier 1 external OEIS problems.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Continued fraction, terminal value $-4$ | `BourasA363347.a`, using `BourasA356360.K` and `nested` | Literal reciprocal and right fold; `Rat.den` |
| Continued fraction, terminal value $-2$ | `BourasA363102.a`, using the same `K` | Literal reciprocal and right fold; `Rat.den` |
| Prime values | `Nat.Prime` and an existential occurrence guard | Includes precisely the primes taken by the sequence |
| Except for $5$ | `BourasA363347.claim` has the guard $p\ne5$ | No exclusion is added to the second claim |
| Indices start at three | Both occurrence sets include $3\le n$ | Matches the OEIS offsets |
| Exactly twice | `BourasA363347.claim` uses `Set.ncard = 2` | Its proof constructs a finite pair |
| Twice or three times | `BourasA363102.claim` uses the disjunction of cardinalities two and three | Its proof constructs a pair or triple |

The natural polynomial `BourasPolynomials.U` is $U(n)=n^2-2$, with truncated
natural subtraction. At $n\ge3$ it agrees with the integer polynomial.
The source's rational fold expressions are represented by the existing frozen
`BourasA356360.nested` and `K` declarations in this module. The public
`BourasA372763OnceRefutation.nested` and `K` owners are textually equal; reusing
them here would require changing or removing those frozen declarations, which
this fix-forward is prohibited from doing. The duplicate-definition findings
are therefore deferred here; no duplicate-retention authorization is claimed.

## Motivation

The results determine unbounded occurrence counts, rather than checking a finite
prefix. A363102 uses the shared arithmetic and root-pair declarations exported
by the A363347 module. In particular `U`, `cast_U`, `U_prime_constraints`, and
`U_prime_of_root` are consumed by `BourasA363102.result`.

## Gap

The literature checks recorded in #18626 and #18627 distinguish these questions
from A363347 Conjectures 1 and 2 and A363102 Conjecture 1, which the OEIS entries
and Adamczewski, arXiv:2608.11941, Table 1, describe as settled. Those earlier
results are not on these modules' dependency paths.
The recorded screen covers the OEIS entries, that article, the Epoch OEIS Open
list, `google-deepmind/formal-conjectures`, and
`google-deepmind/alphaproof-nexus-results`. It found no settlement of the two
multiplicity claims in that scope. Literature completeness is
`ASSUMED-UNVERIFIED`; this is no priority claim.

## Route

For a negative integer tail $x$, put $D=(n-1)x-n(n-2)$. A recurrence for the
numerator gives a linear fractional expression for $K(n,x)$ and a factorial
determinant identity. Their gcd consequence is
$\operatorname{den}(K(n,x))=|D|/\gcd(|D|,n!/2)$.
For $x=-4$, $|D|=(n+1)^2-5$; for $x=-2$, $|D|=n^2-2$.
Factorial divisibility and elementary residue exclusions constrain a surviving
prime denominator. The remaining roots modulo that prime form a pair.
For $x=-2$ a possible extra index satisfies $n^2=2p^2+2$ and is unique.

## Falsifier

A prime $p\ne5$ occurring in A363347 at a number of indices other than two, or
an occurring prime in A363102 at a number of indices other than two or three,
would contradict the corresponding claim. The occurrence guard and the lower
bound on indices are part of both tests.

## Evidence

The settling declarations are
`D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity.BourasA363347.result`
and
`D5.S3.Arith.Congruence.BourasA363102PrimeMultiplicity.BourasA363102.result`.
Their Scribe theorem nodes display the complete claims. The first carries a
`Proved` resolution for `bouras`; the second carries a `Proved` resolution for
`bouras-a363102`.

### Finite computation

[Occurrence-count experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/4d3404c32ec26a2d3d54bf1ed150f97bc218a940/docs/reports/oeis-bouras-continued-fraction-occurrence-counts).
At that immutable revision, run
`python3 docs/reports/oeis-bouras-continued-fraction-occurrence-counts/check.py 300 20000`
from the experiments repository. Exit code: 0.
The SHA-256 of `check.py` is
`05b533313a609bd3bf139aef952a062566625488521351d2d2955731427d9ffb`.
The script reports `RESULT PASS`.
Direct rational-fraction checks cover $3\le n\le300$; the denominator-based
occurrence enumeration covers $3\le n\le20000$ and primes $p\le10000$.
A363347 has 609 primes counted twice, $5$ once at $n=4$, and 619 absent.
A363102 has 600 primes counted twice, three primes counted three times
$(p,n_{\rm extra})=(7,10),(41,58),(239,338)$, and 626 absent.
These are finite computed readings, not a proof of a uniform extension.

### Escape audit

The escape audit is unfinished for all seven public theorem targets:
`cast_U`, `root_fiber_eq_pair`, `square_residue_pair`, `U_prime_constraints`,
`U_prime_of_root`, and the two `result` declarations.
[Issue #21990](https://github.com/the-omega-institute/trureturing/issues/21990)
names their full source owners and the missing dependent source reconstruction,
bridge, variation, sensitivity, and dependence evidence. No `declared_validated`
registration is claimed.

## Triage

### What the settlement shows

1. **Kernel-checked:** `BourasShared.denominator_formula_aux` in the first module
   proves the displayed denominator formula for every $n\ge3$ and every negative
   integer tail. Its parameter is $m=n-3$; no fixed-tail restriction is imposed.
2. **Proved in prose:** for every occurring prime $p\ne5$ in A363347, its
   occurrence set is exactly two modular roots with indices summing to $p-2$.
   The first module's `T_prime_constraints` gives $n+1<p$ and
   $p\mid (n+1)^2-5$ at every occurrence, and `T_prime_of_root` gives the reverse
   implication. `square_residue_pair` at shift one and residue five constructs
   distinct $r,q\ge3$ with $r+q+2=p$; `root_fiber_eq_pair` identifies the complete
   fiber. Substituting the two implications gives precisely the occurrence set
   $\{r,q\}$. These are the intermediate steps used by `BourasA363347.result`;
   its exported statement asserts the cardinality.
3. **Proved in prose, with kernel-checked necessary condition:** for an occurring
   prime in A363102, the indices below $p$ form exactly a pair summing to $p$.
   Apply `square_residue_pair` at shift zero and residue two and use
   `root_fiber_eq_pair`; `cast_U`, `U_prime_constraints`, and `U_prime_of_root`
   identify that fiber with occurrences below $p$. For $n\ge p$,
   `U_prime_constraints` gives $n^2=2p^2+2$. If two natural indices satisfy this
   equation, their equal squares make them equal. This proves at most one extra
   index and yields the pair/triple construction in `BourasA363102.result`.
4. **Computed:** the prime-count distributions and the three extra-index pairs
   for $p\le10000$, $3\le n\le20000$ are exactly the finite readings in Evidence.
   The pinned script, its SHA-256, command, exit code, and rational check range
   are given there.
5. **Open here:** the converse that every prime Pell solution gives a third
   occurrence and the full Newman–Shanks–Williams equivalence are not
   formalized by these results. The exported count claims do not require them.
6. **Open:** infinitude of primes with a third occurrence.
7. **Open here:** the additional A363347 gcd pairing identity and general
   negative-tail occurrence classifications. The denominator formula alone
   does not classify all tails.

The decisive distinction is the possible square deficit after cancellation
against $n!/2$: it is excluded for the $-4$ polynomial and permits the Pell-type
exception for $-2$. The first occurrence-pair identity follows as in item 2;
the additional gcd identity needs control of common small prime factors.
The settlement supplies the two multiplicity conjectures alongside the source's
previously settled prime-value statements. It asserts no new theorem about the
source's other conjectures or the open infinitude question.

## ASSUMED-UNVERIFIED

Literature completeness and historical priority are unverified beyond the
recorded search scope. The experiment certifies only its finite ranges.
Four-slot escape registrations remain unfinished under issue #21990; kernel
proof and registration completion are separate assertions.
