---
slug: oeis-a077739-murthy-zero-indices
bibkey: murthy2002a077739
doi: null
url: https://oeis.org/A077739
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/MurthyA077739Classification.result
---

# The whole Murthy A077739 zero-index classification

## Problem

For each integer $n\geq1$, let $W_n$ contain the positive integers $N$
such that $n\mid N$, the usual decimal digit sum of $N$ is $n$, and the
decimal expansion of $N$ begins and ends with that of $n$. Define
$a(n)=\min W_n$ when $W_n$ is nonempty and $a(n)=0$ otherwise.
[OEIS A077739](https://oeis.org/A077739), revision 5, conjectures

$$
\forall n\geq1,\qquad a(n)=0\quad\Longleftrightarrow\quad
n\in\{11,17,19\}.
$$

The expansion has no leading zeros, permits interior zeros, and permits
the prescribed ends to overlap. There is no bound on $N$ or its length.
Writing $s(x)$ for the decimal digit sum and $w(x)$ for the decimal width,
the formal prefix condition is
$N=n10^k+r$ for some $k,r\in\mathbb N$ with $r<10^k$; the suffix
condition is $N\bmod10^{w(n)}=n$. In particular $k=0$ is allowed.

## Motivation

An existence proof for every nonexceptional index must meet divisibility,
digit sum and both positional conditions simultaneously. A search bound
on witnesses cannot settle this unbounded problem. Conversely, failure to
find a block construction cannot prove that an index is exceptional.
The least-or-zero definition also needs a well-ordering bridge from
existence to the actual sequence value.

## Gap

The source identity and exact quotation are retained in
[the Library note](../Library/Digit/murthy2002a077739.md).
[Issue 30844](https://github.com/the-omega-institute/trureturing/issues/30844)
contains the preregistered external target and its bounded qualification.
The examined repository, pinned Mathlib and public-source searches located
no complete classification. GitHub code search returned HTTP 401;
third-party coverage is incomplete. The original-source conjecture label
and finite examples do not establish an exhaustive literature conclusion.

The formal result closes the entire displayed assertion. Its separate
branches cover $1\leq n\leq9$, all $10\leq n<1000$, the unbounded tail,
and all possible witnesses at the three exceptional indices. The source
sequence uses a minimum, rather than an arbitrary selected witness.

## Route

For $x\in\mathbb N$, define $s(x)=\sum\operatorname{digits}_{10}(x)$.
Decimal concatenation satisfies $s(x10^L+y)=s(x)+s(y)$ for $y<10^L$.
Concatenating multiples of $n$ preserves divisibility. Starting with a
literal $n$ block preserves the prefix through further concatenations;
appending a final $n$ supplies the suffix. Thus middle blocks, each a
multiple of $n$, give a witness whenever their digit sums total $n-2s(n)$.

**Symbolic tail.** For $0<n\leq10^L$, put $B_L=n(10^L-1)$.
The decomposition

$$
B_L=(n-1)10^L+(10^L-n)
$$

and the padded decimal complement identity give $s(B_L)=9L$.
For $n\geq1000$, let $d=w(n)\geq4$. The proof establishes

$$
9d^2+81d\leq10^{d-1}\leq n,\qquad s(n)\leq9d.
$$

Since $n\equiv s(n)\pmod9$, the natural number
$q=(n-10s(n))/9$ is well-defined with exact division, and
$q\geq d(d-1)$. Set $b=q\bmod d$ and $a=\lfloor q/d\rfloor-b$.
The bound ensures $a\geq0$, and $q=ad+b(d+1)$. Concatenate a first
$n$, eight more copies of $n$, $a$ copies of $B_d$, $b$ copies of
$B_{d+1}$, and a final $n$. Its digit sum is

$$
10s(n)+9ad+9b(d+1)=n.
$$

Every block is divisible by $n$. This constructs an admissible positive
integer for every $n\geq1000$, with no finite witness-length cutoff.

**Finite branch.** For $1\leq n\leq9$, take $N=n$.
For each of the 987 nonexceptional indices $10\leq n<1000$, a retained
row of pairs $(j,c)$ specifies $c$ copies of the middle block $jn$.
The generic checker tests

$$
2s(n)+\sum_{(j,c)}c\,s(nj)=n.
$$

The source array has 1000 index slots; the kernel-checked theorem skips
indices below ten and the three exceptions. The 987 required rows contain
1643 pairs in total, with largest multiplier $j=195$. At $n=18$ the
middle is empty. `certificate_sound` converts a successful check into a
witness using the general concatenation theorem. The terminal theorem
consumes this branch together with the symbolic tail; the table is not a
finite replacement for the universal conclusion.

**Exclusions.** At $n=11$, the suffix writes $N=11+100q$.
Digit sum and divisibility force $s(q)=9$ and $11\mid q$. Evaluating
the digits of $q$ at $-1$ gives an odd integer between $-9$ and $9$
divisible by 11, a contradiction.
For 17 and 19, the empty appended block has the wrong digit sum, and
one-digit overlap is impossible. Every remaining possibility has

$$
N=n10^{k+2}+100M+n,\qquad s(N)=2s(n)+s(M).
$$

For 19 the ends already contribute 20. For 17 they contribute 16,
so $s(M)=1$ and hence $M=10^j$. Divisibility would force 17 to divide
a power of ten, which primality excludes. These are arguments against
arbitrary witnesses, including overlaps, rather than failed searches.

**Minimum bridge.** The formal sequence is
`a n = sInf {N : Nat | Witness n N}`. Every witness is positive.
`Nat.sInf_mem` and `Nat.sInf_eq_zero` yield
$a(n)=0\leftrightarrow\neg\operatorname{Admissible}(n)$, so the
existence classification proves the displayed least-or-zero assertion.

## Falsifier

An admissible positive $N$ for one of 11, 17 or 19 would refute the
exclusion direction. A nonexceptional $n\geq1$ without any admissible
$N$ would refute the existence direction. A mismatch between the source
decimal conventions and the formal prefix/suffix predicate, a missing
certificate row, an invalid block-sum identity, a tail-parameter failure,
or an unjustified minimum bridge would invalidate this proof route.
Finite search failure alone is not either mathematical falsifier.

## Evidence

The mathematical source is
`D5/S1/Digit/Admissibility/MurthyA077739Classification.lean`.
Its sole public theorem is `result : claim`, where `claim` is exactly the
all-positive-index least-or-zero assertion above. The corresponding
Blueprint Scribe binds this theorem to this problem with
`OpenProblemResolutionClaim` and `ResolutionKind.Proved`. The frozen
state is maintained by the canonical deposit writer; the dossier is not a
second proof or state ledger. The theorem's axiom closure consists only
of `Classical.choice`, `Quot.sound` and `propext`.

The independent declaration assessment classifies the following private
helpers as consumed `bind-only` organization:

| Helper | Actual consumer |
| --- | --- |
| `sum_step` | `sum_cons`, `sum_complement`, `sum_one` |
| `sum_cons` | `sum_add_shift`, `sum_complement` |
| `sum_add_shift` | `sum_concat`, `sum_multiple_nines`, `two_end_decomposition` |
| `sum_concat` | `extend_properties`, `from_blocks` |
| `begins_concat` | `extend_properties`, `from_blocks` |
| `begins_self` | `from_blocks`, `admissible_small` |
| `dvd_concat` | `extend_properties`, `from_blocks` |
| `a_zero_iff` | `result` |
| `digit_sum_width` | `tail_parameters` |
| `sum_zero` | `sum_one` |
| `two_end_decomposition` | `not_admissible_seventeen`, `not_admissible_nineteen` |
| `not_admissible_nineteen` | `classification` |
| `certificate_blocks` | `certificate_sound` |

The remaining proof helpers, including `tail_parameters`,
`admissible_tail`, `classification` and the expanded public `result`,
are assessed as `content`. The consumed helpers do not supply separate
new-content or external-problem counts. The checker instance is
`certificateData`, with general soundness and an unbounded terminal
consumer. Admission is the complete external open-problem resolution.

The literal certificate rows are stored in the adjacent
`MurthyA077739CertificateLow.entries` (indices 0 through 499) and
`MurthyA077739CertificateHigh.entries` (indices 500 through 999) modules.
The private `certificateData` appends these arrays in that order, preserving
all 1000 index positions and 1643 multiplier-count pairs. Both exported
definitions are consumed proof data, with no independent theorem or
external-problem count. The original `certificates_checked` kernel
reduction and the general `certificate_sound` consumer validate the
assembled data; the storage modules alone assert no admissibility result.

The retained Reg mirror is
`Reg/D5/S1/Digit/Admissibility/MurthyA077739Classification.lean`.
Its four-slot audit is `declared_validated`, with exact
`source-equivalence` reconstruction and lawful dependent-family template
enrollment. The actual realization reads $a(n)$ for every natural $n$;
the law quantifies over every $n\geq1$. A constantly zero realization
fails at one, supplying whole-family variation and sensitivity. Actual
dependence uses the differing readouts at 11 and one. The typed
continuation is `.unknown`; this records an unknown residual, not a
theorem of undecidability or inexhaustibility.

## Triage

`theorem`. The resolution is the entire source classification: existence
at every nonexceptional positive index, nonexistence at all three
exceptions, and the bridge to the minimum-or-zero sequence.

The block mechanism explains why the tail is uniformly admissible:
two consecutive digit-sum denominations $9d$ and $9(d+1)$ absorb the
residual after ten literal copies of $n$. The threshold 1000 and the
multiplier bound 195 are sufficient bounds of this proof, not assertions
of optimality. Neither gives an upper bound on the least witness.
The method suggests questions about witness size, other radices and
other prescribed ends, but those require their own statements and proofs.
No additional external open problem is claimed; a qualified successor
remains pending literature screening.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and worldwide publication priority remain
unverified. The bounded search and the current conjecture label do not
exclude every independently published solution. The result does not
compute every least witness, prove optimal construction lengths, classify
other bases, or settle neighboring external questions. The Reg unknown
continuation supplies no further mathematical conclusion.
