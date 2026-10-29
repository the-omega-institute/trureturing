---
slug: bouras-a363102
bibkey: bouras2023continuedfractionmultiplicity
doi: null
url: https://oeis.org/A363102
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BourasA363102PrimeMultiplicity
---

# Two or three prime occurrences in Bouras A363102

## Problem

M. Bouras, OEIS A363102, COMMENTS, Conjecture 2:

> Conjecture 2: All prime numbers appear either twice (same as A356247 and A357127) or three times.

For $n\ge3$, $a(n)$ is the positive reduced denominator of the rational
continued fraction $1/(2-3/(3-4/(\cdots-n/(-2))))$.
The claim quantifies over primes that occur, as specified in preregistration
#18627. It does not assert that every prime occurs. This dossier anchors only
Conjecture 2; the $-4$ sequence has its own [dossier](bouras.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Rational continued fraction with tail $-2$ | `BourasA363102.a` uses `BourasA356360.K n (-2)` and `Rat.den` | Literal reciprocal right fold |
| Prime values | `Nat.Prime` and the existential occurrence hypothesis in `claim` | Excludes primes absent from the sequence |
| OEIS offset $n=3$ | $3\le n$ in the occurrence guard and counted set | All larger indices are included |
| Twice or three times | The disjunction of `Set.ncard = 2` and `Set.ncard = 3` | The proof exhibits a pair or a triple |

## Motivation

The result determines the occurrence count for every prime value, uniformly in
the prime and in the index. It consumes the shared polynomial, cast, prime
constraints, reverse-root theorem and root-pair theorems exported by
`BourasA363347PrimeMultiplicity`.

## Gap

The screen recorded in #18627 found no settlement in the OEIS entry,
Adamczewski's arXiv:2608.11941, the Epoch OEIS Open list, or the named Google
DeepMind formal-conjecture and AlphaProof result collections. The source's
prime-value Conjecture 1 is already literature-attested; it is not a dependency
of this module. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The shared denominator formula gives
$a(n)=(n^2-2)/\gcd(n^2-2,n!/2)$ for $n\ge3$.
`U_prime_constraints` says that an occurring prime is at least seven, divides
$n^2-2$, and either exceeds $n$ or satisfies $n^2=2p^2+2$.
The two roots of $n^2\equiv2\pmod p$ below $p$ are paired by $n\mapsto p-n$.
`U_prime_of_root` turns these two roots into occurrences. Equal natural squares
make an index above $p$ unique, so the total is two or three.

## Falsifier

An occurring prime whose full index set at $n\ge3$ has cardinality other than
two or three contradicts the literal claim. An absent prime is outside its
occurrence hypothesis.

## Evidence

`D5.S3.Arith.Congruence.BourasA363102PrimeMultiplicity.BourasA363102.result`
proves the complete occurrence-count claim. The Scribe node displays its full
proposition and carries a `Proved` resolution for this dossier.

The [pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/4d3404c32ec26a2d3d54bf1ed150f97bc218a940/docs/reports/oeis-bouras-continued-fraction-occurrence-counts)
is run with
`python3 docs/reports/oeis-bouras-continued-fraction-occurrence-counts/check.py 300 20000`
from the experiments repository; exit 0. Its script SHA-256 is
`05b533313a609bd3bf139aef952a062566625488521351d2d2955731427d9ffb`.
The script reports `RESULT PASS`.
Direct rational checks cover $3\le n\le300$. Occurrence enumeration covers
$3\le n\le20000$ and $p\le10000$: 600 primes occur twice, three occur three
times, and 626 are absent. The triples have $(p,n_{\rm extra})$ equal to
$(7,10),(41,58),(239,338)$.

The escape audit is unfinished for `BourasA363102.result` and the six public
theorem targets in the shared module. [Issue #21990](https://github.com/the-omega-institute/trureturing/issues/21990)
lists the missing source reconstruction and bridge/intervention evidence.
No `declared_validated` registration is claimed.

## Triage

### What the settlement shows

- **Kernel-checked:** `BourasA363102.result` proves that every occurring prime
  has two or three indices. `U_prime_constraints` gives the necessary Pell-type
  equation $n^2=2p^2+2$ at each extra index.
- **Proved in prose:** `square_residue_pair` at shift zero and residue two,
  together with `root_fiber_eq_pair`, `cast_U`, and `U_prime_of_root`, gives the
  complete pair below $p$, with sum $p$. Any two extra indices have equal
  squares $2p^2+2$ and hence are equal. These are the intermediate statements
  used to construct the pair or triple in the settling proof.
- **Computed:** the exact finite distributions and third-index pairs are the
  experiment readings in Evidence, within its stated ranges.
- **Open here:** the converse from a prime Pell solution to a third occurrence
  and the complete Newman–Shanks–Williams equivalence are not formalized.
- **Open:** infinitude of primes with a third occurrence.
- The common negative-tail denominator identity, the A363347 root pairing,
  the finite distributions of both sequences, and the open gcd-pairing and
  general-tail classification questions are treated, with their evidence
  kinds, in the [family Triage](bouras.md#triage).

The square deficit after factorial cancellation explains why this sequence
permits a third occurrence while the $-4$ sequence has only the root pair.
The result settles the count claim alongside the previously known prime-value
statement. It asserts no new result about infinitude or the source's other
conjectures.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain unverified beyond the recorded
screen. The experiment has only finite scope. Escape registration is unfinished
under #21990 and is distinct from the kernel-checked occurrence theorem.
