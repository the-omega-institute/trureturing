---
slug: murthy-a087371-bounded-exponent
bibkey: murthy2003a087371
doi: null
url: https://oeis.org/A087371
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result
---

## Problem

Amarnath Murthy's OEIS A087371, revision 7, NAME (unpaginated), states:
"Smallest k such that 10^k + 2n-1 is a prime >10, or 0 if no such k exists.
Index of the smallest power of 10 which when increased by the n-th odd number yields a prime."
COMMENTS states: "Conjecture: There exists a finite M such that a(n) < M for all n."
The entry is from 2003 and has offset one. The complete assertion is preregistered in
[#30802](https://github.com/the-omega-institute/trureturing/issues/30802), with its
[scope commitment](https://github.com/the-omega-institute/trureturing/issues/30802#issuecomment-6892890030).

For every natural index $n\ge1$, let $a(n)$ be the least positive natural $k$
such that $10^k+2n-1$ is prime and strictly greater than $10$, or exactly $0$
if no such positive exponent exists. The conjecture is
$\exists M\in\mathbb N,\ \forall n\in\mathbb N,\ n\ge1\Rightarrow a(n)<M$.
Both quantifiers are unbounded, and one strict bound must serve all indices.
Exponent zero cannot satisfy the source event: its candidate is $2n$, whose
only possible prime value is $2$, below the required threshold.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| All indices with offset one | `claim` quantifies over every natural `n` with `1 ≤ n`. |
| Decimal power plus the n-th odd number | `a` uses natural `10 ^ k + 2 * n - 1`; on the source domain this subtraction is exact. |
| Prime strictly greater than ten | Both `Nat.Prime` and `10 < 10 ^ k + 2 * n - 1` occur in the qualifying predicate. |
| Least positive exponent, zero if none | `Nat.find` under the complete existence guard; the other branch is `0`. |
| One finite strict uniform bound | `claim : Prop := ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → a n < M`. |
| Refutation of that entire assertion | The closed theorem `result : ¬ claim`. |

The total definition outside $n\ge1$ introduces no extra premise or restriction
on the conjecture. No cutoff on $n$ or $k$, and no assumption that a success
exists for every index, is added.

## Motivation

A finite numerical prefix cannot bound the waiting exponent over every odd
offset. Consecutive primes separated by a sufficiently long gap let a chosen
large power become the first successful exponent. This tests the actual
leastness event, including the strict prime threshold and empty-set branch.

## Gap

The source is an older published small conjecture, qualified in the first tier
within the recorded search scope. The source entry retains the conjecture;
bounded literature and library searches found no earlier complete settlement
in the searched forms. This is bounded qualification, not a priority claim.
The mathematical target is the full uniform-bound assertion, not a finite
window or a version conditional on successful indices.

## Route

For any $K\ge1$, apply the existing frozen
`D5/S3/Arith/Primes/PrimeGap.exists_primeGap_ge` at $10^K$ to obtain consecutive
primes $q<p$ with $p-q\ge10^K$. The upper prime is odd and strictly greater
than ten. Its difference from the even number $10^K$ is a positive odd
integer $2m+1$. Set $n=m+1\ge1$; then $10^K+2n-1=p$.
For every natural $j<K$, the candidate $10^j+2n-1$ lies strictly between
$q$ and $p$, and is therefore composite. Thus $a(n)=K$.
Taking $K=M+1$ contradicts any proposed strict uniform bound $M$.

The exact settling GID is
`D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result`.
Its `proof_shape` is `bind-only`, `escape_witness` is `none`, and
`admission_basis` is `open-problem-resolution` under #30802.
The prime-gap theorem is reused directly, without a duplicate proof or a new
helper result. Its declaration identity is
`sha256:26b3a3c763959a61efe82acd853d7020ac93f79dc7277f258b98e25b989f31de`.
The designated closed-negation result is exempt from four-slot escape
registration; the module has no other authored theorem.

## Falsifier

Source correspondence would fail if the source excluded constructed positive
indices, required a different exponent convention, omitted leastness, or used
a different prime threshold. All of these clauses are explicit above and in
the owning Library note. The gap argument must establish both success at $K$
and failure at every earlier positive exponent; success alone would not suffice.

## Evidence

The kernel evidence is the frozen `result`, with necessary definitions `a`
and `claim`, in `D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.lean`.
Its compiled type is literally `Not claim`, with no free hypotheses, and its
axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.
The universal construction of first successes is the local `hsurj` within
that proof, not a separately delivered theorem. The corresponding Blueprint
mirrors all three public declarations and binds this dossier as `Refuted`.
Source identity and the exact quotations are in
[the Library note](../Library/ArithUnits/murthy2003a087371.md).

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
(404) were unavailable. These limitations prevent an exhaustive absence,
priority or originality conclusion.

## Triage

| Assertion or implication | Evidence and boundary |
| --- | --- |
| The published strict uniform-bound conjecture is false. | Proved by the complete closed `result`; no conditional residue remains in this assertion. |
| Every positive $K$ occurs as a first successful exponent. | Established by local `hsurj` in the same kernel proof, with an index depending on $K$. |
| Arguments requiring a uniform cap on these exponents. | That hypothesis fails; consequences for any particular external argument require checking its actual use. |
| Which indices have value zero, or how often each value occurs. | Not classified by this result. |
| An explicit size bound for the constructed index, density, or a theorem for arbitrary bases. | Not supplied by this settlement. |
| Completeness of the literature search and publication priority. | ASSUMED-UNVERIFIED within the limits above. |

The two Murthy sequences have separate source assertions and separate closed
refutations. Reusing the same frozen prime-gap supplier does not constitute
an additional general theorem or establish a relation between their indices.

## ASSUMED-UNVERIFIED

The correspondence to the published wording and its positive-exponent
convention is a source-fidelity judgement, not a Lean theorem about publication
text. Literature completeness and priority remain unverified because the
search is bounded and the unavailable services listed above supply no negative
evidence. No empirical distribution, index-size estimate or classification of
the zero branch is asserted.
