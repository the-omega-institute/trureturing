---
slug: murthy-a087372-bounded-exponent
bibkey: murthy2003a087372
doi: null
url: https://oeis.org/A087372
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result
---

## Problem

Amarnath Murthy's OEIS A087372, revision 9, NAME (unpaginated), states:
"Smallest k such that 3^k + 2n is a prime, or 0 if no such k exists.
Index of the smallest power of 3 which when increased by the n-th even number yields a prime."
COMMENTS states: "Conjecture: There exists a finite M such that a(n) < M for all n."
The entry is from 2003 and has offset one. The complete assertion is preregistered in
[#30801](https://github.com/the-omega-institute/trureturing/issues/30801), with its
[scope commitment](https://github.com/the-omega-institute/trureturing/issues/30801#issuecomment-6892889812).

For every natural index $n\ge1$, let $a(n)$ be the least positive natural $k$
such that $3^k+2n$ is prime, or exactly $0$ if no such exponent exists.
The conjecture is
$\exists M\in\mathbb N,\ \forall n\in\mathbb N,\ n\ge1\Rightarrow a(n)<M$.
The source's EXAMPLE fixes positive exponents: "a(23) = 3 as 3^3 + 46 = 73
is a prime but 46+3 and 46+9 are not." Allowing exponent zero would give
the prime $47$ and contradict that example.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| All indices with offset one | `claim` quantifies over every natural `n` with `1 ≤ n`. |
| Ternary power plus the n-th even number | `a` uses exactly `3 ^ k + 2 * n`. |
| Prime candidate | `Nat.Prime (3 ^ k + 2 * n)` occurs in the qualifying predicate. |
| Least positive exponent, zero if none | `Nat.find` under the complete existence guard; the other branch is `0`. |
| One finite strict uniform bound | `claim : Prop := ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → a n < M`. |
| Refutation of that entire assertion | The closed theorem `result : ¬ claim`. |

Both quantifiers are unbounded. The total definition outside the source
domain introduces no extra premise. The claim includes indices with no
successful exponent and does not assume a prime exists at every index.

## Motivation

The source asks for a bound uniform over all even offsets. Large consecutive
prime gaps allow a prescribed positive exponent to become the first success,
so a finite prefix cannot establish the proposed cap. The construction must
control every earlier positive exponent, rather than merely find a later prime.

## Gap

This is an older published small conjecture, qualified in the first tier
within the recorded search scope. The source retains its conjecture line;
bounded literature and library searches found no earlier complete settlement
in the searched forms. The target is its complete uniform assertion, including
the source convention on exponents and the exact empty-set value.
No universal absence or priority conclusion follows from this qualification.

## Route

For any $K\ge1$, apply the existing frozen
`D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge` at $3^K$. It gives consecutive
primes $q<p$ with $p-q\ge3^K$. The upper prime is odd; its difference from
the odd number $3^K$ is an even integer at least two. Write it as $2n$,
so $n\ge1$ and $3^K+2n=p$. For every positive $j<K$, the candidate
$3^j+2n$ lies strictly between $q$ and $p$, hence is composite.
The first successful exponent is therefore exactly $K$.
Taking $K=M+1$ contradicts any proposed bound $M$.

The exact settling GID is
`D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result`.
Its `proof_shape` is `bind-only`, `escape_witness` is `none`, and
`admission_basis` is `open-problem-resolution` under #30801.
The direct frozen supplier's declaration identity is
`sha256:26b3a3c763959a61efe82acd853d7020ac93f79dc7277f258b98e25b989f31de`.
It is directly reused without a copied factorial proof or new helper theorem.
The designated closed-negation result is exempt from four-slot escape
registration; the module has no other authored theorem.

## Falsifier

Source correspondence would fail if the sequence allowed exponent zero,
discarded unsuccessful indices, or imposed a cutoff on indices or exponents.
The source example and complete definition above rule out those translations.
The proof must establish the absence of every earlier positive success;
an arbitrary prime-producing exponent alone would not refute the bound.

## Evidence

The kernel evidence is the frozen `result`, with necessary definitions `a`
and `claim`, in `D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.lean`.
Its compiled type is literally `Not claim`, with no free hypotheses, and its
axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.
The local `hsurj` establishes every positive first-success value within the
same proof; no additional public theorem is delivered for that assertion.
The Blueprint mirrors all three declarations and binds this dossier as `Refuted`.
Source identity and exact quotations are in
[the Library note](../Library/ArithUnits/murthy2003a087372.md).

### Bounded literature qualification

The qualification covers the live OEIS JSON and original internal entry,
repository sources including private declarations, and pinned Mathlib.
Exact-pair arXiv search `all:A087371 OR all:A087372` returned zero records;
`all:"least exponent" AND all:prime` returned two unrelated abstracts.
Crossref exact-ID searches returned zero records for each ID in the supplied
readings; the independent A087372 request was rate limited (429).
Stack Exchange searches for each ID on math and MathOverflow, and for
`Murthy prime exponent` on both sites, returned zero items with no further page.
The caller's authenticated GitHub Lean exact-ID queries each returned
`total=0`, `incomplete=false`. No complete resolution was found in these scopes.
OpenAlex was rate limited (429); general web searches produced challenges,
an interstitial or unrelated RSS results. LeanSearch (403) and Reservoir
(404) were unavailable. None of these unavailable results establishes absence.

## Triage

| Assertion or implication | Evidence and boundary |
| --- | --- |
| The complete published strict uniform-bound conjecture is false. | Proved by the closed `result`, over all source indices. |
| Every positive $K$ occurs as a first successful exponent. | Established by local `hsurj` in the kernel proof, with a constructed index depending on $K$. |
| Arguments requiring a uniform bound on the least exponent. | That hypothesis fails; the effect on any particular argument requires checking its use. |
| Which indices have value zero, or multiplicities of positive values. | Not classified here. |
| An explicit bound on the index, density, or arbitrary-base generalization. | Not supplied by this settlement. |
| Completeness of the literature search and priority. | ASSUMED-UNVERIFIED within the bounded search above. |

This refutation does not depend on a theorem about the decimal sequence.
The shared frozen prime-gap supplier is a reused prerequisite, not a new
general-theorem contribution or an identification of the two index sets.

## ASSUMED-UNVERIFIED

Source fidelity, including the positive-exponent convention fixed by EXAMPLE,
is a judgement about the publication rather than a theorem about its text.
The searches are bounded and several services were unavailable, so exhaustive
literature coverage, priority and originality remain unverified. No density,
index-size estimate or classification of permanent failures is asserted.
