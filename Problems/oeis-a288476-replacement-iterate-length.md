---
slug: oeis-a288476-replacement-iterate-length
bibkey: kimberling2017a288476
doi: null
url: https://oeis.org/A288476
triage: theorem
motivation_gids:
  - D5/S1/Words/KimberlingA288476Length.result
---

## Problem

Clark Kimberling's OEIS A288476 COMMENTS conjecture states:
"Conjecture:  a(n) is the number of letters (0's and 1's) in the n-th
iteration of the mapping 00->0101, 1->011, starting with 00; see A288473."
The sequence is independently defined by $a_0=2,a_1=4,a_2=8$ and
$a_{n+3}=a_{n+2}+4a_{n+1}-2a_n$ over integers.
The source and complete target are preregistered in
[#28179](https://github.com/the-omega-institute/trureturing/issues/28179).
The [Library source note](../Library/Rewriting/kimberling2017a288476.md)
records the original and current revision locators and licenses.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every integer index $n\ge0$ | `result (n : ℕ)`, including zero and both parities |
| Start with 00 | `sourceIter n := sourceScan^[n] [false,false]` |
| Replace 00 by 0101 and 1 by 011 | Native recursive `sourceScan`, in that match order |
| One nonoverlapping original-input pass | Every recursive call consumes only the remaining original input; unmatched 0 is retained |
| Number of 0s and 1s | `List Bool.length`, with false=0 and true=1 |
| Independently defined $a_n$ | `recurrence : LinearRecurrence ℤ`, order 3, ascending coefficients `![-2,4,1]`; `recurrenceSeq` has initial data `![2,4,8]` |
| Complete equality | `((sourceIter n).length : ℤ) = recurrenceSeq n`, with no coding hypothesis or cutoff |

The identical length assertions in A288473 and A288551 belong to this
same event. Position, frequency and limiting-word existence assertions
are outside its scope.

## Motivation

The native all-index result connects an actual nonoverlapping string
operation to an independently specified scalar recurrence. The proposed
admission basis is `open-problem-resolution` for #28179, and `utility: none`:
this is an unbounded symbolic theorem, with no positive finite certificate.
The author classification is `proof_shape: bind-only`: after inlining the
supporting declarations, the finite boundary cases, existing `List.foldr_hom`,
semiconjugacy, iterate representation, length normalization and recurrence
uniqueness supply the proof. The external open-problem resolution exception
is the admission basis; no generic escape witness is claimed. Every private
supporting theorem is used by the native result.

## Gap

The scanner is not a homomorphism on arbitrary binary concatenations:
scanning 0 followed by 0 emits 0101, whereas scanning the two singletons
separately emits 00. A valid bridge must control code boundaries for
arbitrary following suffixes.

## Route

Use code words $h(D)=00,h(E)=01,h(O)=1$ and the ternary substitution
$\sigma(D)=EE,\sigma(E)=DOO,\sigma(O)=EO$.
For every code letter $c$ and binary suffix $v$,
$R(h(c)v)=h(\sigma(c))R(v)$. The existing `List.foldr_hom` gives this identity
for every finite ternary word. The existing Mathlib semiconjugacy iteration
theorem transports it to all native iterates.

Let $A_n,B_n,C_n$ be the integer lengths of the encoded iterates of
$D,E,O$. Direct applications of the frozen polymorphic `image_add`,
`image_one` and `subst_append` yield
$A_{n+1}=2B_n$, $B_{n+1}=A_n+2C_n$, $C_{n+1}=B_n+C_n$.
Elimination gives the stated cubic recurrence. Mathlib's
`LinearRecurrence.eq_mk_of_is_sol_of_eq_init` identifies it with $a_n$.
All subtraction occurs in integers.

## Falsifier

An actual native source iterate whose length differs from the independent
recurrence would refute the conjecture. Failure of arbitrary binary
concatenation is a counterexample to an invalid proof shortcut, not to
the source assertion.

## Evidence

The mathematical source is
[KimberlingA288476Length.lean](../D5/S1/Words/KimberlingA288476Length.lean),
with its corresponding Scribe. The sole public theorem is `result`.
Its author-written source audit is at the corresponding
`Reg/D5/S1/Words/KimberlingA288476Length.lean`; registration status requires
the compiled current binding evidence. No source mirror or publication
completion is asserted here.

## Triage

### What the settlement shows

| Conclusion | Status and scope |
| --- | --- |
| Native source length equals the independent recurrence at every natural index | proved in `result`, including zero and both parities |
| Boundary-safe code intertwining for arbitrary finite code words and arbitrary binary suffixes at each code-letter boundary | proved in the private supporting declarations, by the source boundary equations and existing fold homomorphism |
| The length assertions repeated in A288473 and A288551 | the same proved conclusion, one event |
| Position and frequency conjectures, limiting-word existence and other replacement rules | open in this delivery |

The decisive relation is the boundary-safe code intertwining. No limiting-word
hypothesis is needed for the length theorem.

The recoding method is standard prior art. The proposed new result is
this exact external source assertion, not a new generic method or a
worldwide originality claim.

## ASSUMED-UNVERIFIED

The literature screen and deduplication are bounded and do not establish
worldwide priority or exclude unindexed aliases. Independent source
mirror, canonical emission and first freeze, review, required CI, merge,
first dev push and completion gates remain outside StageA.
