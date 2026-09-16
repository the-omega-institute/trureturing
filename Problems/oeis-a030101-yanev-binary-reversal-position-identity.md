---
slug: oeis-a030101-yanev-binary-reversal-position-identity
bibkey: yanev2017a030101
doi: null
url: https://oeis.org/A030101
triage: theorem
motivation_gids:
  - D5/S1/Digit/YanevBinaryReversalPositionIdentity.result
---

# Yanev's position identity for binary reversal

## Problem

OEIS A030101, OFFSET (`%O`, verbatim):

> 0,4

OEIS A030101, initial sequence line (`%S`, verbatim):

> 0,1,1,3,1,5,3,7,1,9,5,13,3,11,7,15,1,17,9,25,5,21,13,29,3,19,11,27,7,

OEIS A030101, NAME (`%N`, verbatim):

> a(n) is the number produced when n is converted to binary digits, the binary digits are reversed and then converted back into a decimal number.

Ralf Stephan's A030101 recurrence (`%F`, verbatim):

> a(n) = 0, a(2n) = a(n), a(2n+1) = a(n) + 2^(floor(log_2(n)) + 1). For n > 0, a(n) = 2*A030109(n) - 1. - _Ralf Stephan_, Sep 15 2003

Velin Yanev's A030101 conjecture (`%F`, verbatim):

> Conjecture: a(n) = 2*w(n) - 2*w(A053645(n)) - 1 for n > 0, where w = A264596. - _Velin Yanev_, Sep 12 2017

OEIS A030101, AUTHOR (`%A`, verbatim):

> _David W. Wilson_

OEIS A264596, NAME (`%N`, verbatim):

> Let S_n be the list of the first n nonnegative numbers written in binary, with least significant bits on the left, and sorted into lexicographic order; a(n) = position of n in S_n, starting indexing at 0.

Heinz's A264596 recurrence (`%F`, verbatim):

> a(2n) = a(n), a(2n+1) = a(n) + n+1, a(0) = 0. - _Alois P. Heinz_, Nov 19 2015

OEIS A053645, NAME (`%N`, verbatim):

> Distance to largest power of 2 less than or equal to n; write n in binary, change the first digit to zero, and convert back to decimal.

OEIS A053645, defining formula (`%F`, verbatim):

> a(n) = n - 2^A000523(n).

The formal definitions are:

```lean
def w : ℕ → ℕ :=
  Nat.binaryRec 0 (fun bit n previous => if bit then previous + n + 1 else previous)

def stripTop (n : ℕ) : ℕ := n - 2 ^ Nat.log 2 n

def rev : ℕ → ℕ :=
  Nat.binaryRec 0 fun bit n previous =>
    if bit then if n = 0 then 1 else previous + 2 ^ (Nat.log 2 n + 1) else previous
```

The proved statement is:

```lean
theorem result (n : ℕ) (hn : 1 ≤ n) :
    rev n + 2 * w (stripTop n) + 1 = 2 * w n
```

The source writes the result with subtraction on the right. Lean natural
subtraction truncates, so the theorem moves the two subtracted quantities to
the additive side. It proves the source equality together with the
non-negativity needed for the source subtraction. The printed recurrence
begins `a(n) = 0`, rather than `a(0) = 0`; its initial sequence value and the
rest of the recurrence identify the intended zero boundary used by `rev`.

Not claimed: A264596 contains a separate Yanev conjecture dated Sep 12 2017.
That conjecture is outside this dossier and is not asserted or resolved here.

## Motivation

The conjecture connects two independent views of a binary word: reversal of
its digits and its lexicographic rank when the least significant digit is read
first. The theorem establishes the identity for every positive natural input,
not merely a finite range.

## Gap

The A030101 text endpoint read on 2026-09-16 still labels Yanev's formula
`Conjecture` and contains no settlement line. The target and the content-form
escape witness were registered in issue #8214 before this implementation.
Repository searches over `D5`, `Blueprint`, `Library`, and `Problems` found no
A030101 or A264596 result before this addition. A statement-shape search in
the repository and a binary-reversal/lexicographic-position search in pinned
Mathlib found no dominating theorem in those searched scopes.

## Route

1. Define `w` by Heinz's even and odd recurrence and `rev` by Stephan's even
   and odd recurrence, both through `Nat.binaryRec`.
2. Use binary induction. At each positive half-index, `Nat.log_two_bit`
   identifies the new leading power and `Nat.pow_log_le_self` bounds the power
   removed by `stripTop`.
3. Show locally that `stripTop` doubles in the even branch and doubles then
   adds one in the odd branch. Apply the corresponding `w` recurrence and the
   induction hypothesis.
4. In the odd branch, use `Nat.sub_add_cancel` for the leading power and close
   the resulting natural arithmetic identity.

`result` has `proof_shape: content`. Its escape witness is form (2), the
public conclusion itself, produced on the live binary-induction path. There
are no frozen project dependencies and no separate helper declarations. The
module has `admission_basis: escape-witness`. All four declarations have
`utility: none`: the definitions are symbolic recurrences and the theorem is
an unbounded universal identity, not a finite enumeration, checker, numeric
reduction, or certified instance.

## Falsifier

Any positive natural `n` for which
`rev n + 2 * w (stripTop n) + 1 ≠ 2 * w n` would refute the theorem. A mismatch
between any formal definition and its displayed OEIS recurrence would refute
the source interpretation independently of the theorem.

## Evidence

The Lean kernel checks the binary-induction proof under the pinned toolchain.
The Scribe document mirrors each public definition and the full theorem. The
canonical repository doors record the exact source-bound Lean report, emitted
Markdown, freeze state, and admission result.

## Triage

`theorem`; resolution `proved`. The formal result settles the displayed
A030101 identity for every positive natural input.

## ASSUMED-UNVERIFIED

The source endpoints establish what OEIS displayed on 2026-09-16, not an
exhaustive world-literature priority claim. The bounded repository and pinned
Mathlib searches establish only `not-found-in-searched-scope`.
