---
slug: campbell-currie-rampersad-eq-11
bibkey: campbell2025reduced
doi: 10.48550/arXiv.2509.16034
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/ThueMorseReducedAbelianEven
---

# Equation (11) for the reduced abelian complexity of the Thue-Morse word

## Problem

Write `rho(n)` for the reduced abelian complexity of the Thue-Morse word: the
number of classes of length-`n` factors, where two factors are equivalent when
collapsing each maximal constant run to one letter leaves words of equal length
that are rearrangements of one another. Campbell, Currie and Rampersad display

    |rho(4n+2) - rho(4n)| = 0  if t(n+1) = t(3n+1),  and 1 otherwise,

as equation (11) in the Conclusion of arXiv:2509.16034v1, with the sentence "It
appears that (11) holds", and state a few lines later that they leave proving it
as an open problem. Their indices start at one; the zero-indexed reading, which
the caller measured rather than assumed, is `t(n) = t(3n)`.

## Motivation

The odd-index half of the same paragraph is already carried here as
`Problems/thue-morse-reduced-abelian-odd`, together with the frozen module
`D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd`. That module already
supplies the all-start factor definitions, the run-collapsed Parikh vector, the
code that decides equivalence, and the odd recurrence. Equation (11) is the
even-index counterpart and was the nearest unclaimed item in the same paragraph.

## Gap

The odd recurrence follows from a bijection between codes at lengths `2n+1` and
`n+1`. No such bijection is available at even lengths: the two lengths `4n` and
`4n+2` carry genuinely different class counts, and their difference is one of
zero and one according to a condition on two Thue-Morse letters. So the even
case needs the spectrum of the codes, not a length-to-length correspondence.

## Route

Let `alternations n s` count the letter changes in the length-`n` factor at
start `s`, and let `minAlternations n` and `maxAlternations n` be its extremes
over all starts. Two steps carry the argument.

First, the parity of the sum of the two extremes is governed by two Thue-Morse
letters: `(minAlternations n + maxAlternations n) % 2` is zero exactly when
`thueMorse n = thueMorse (3 * n)`. The proof is a strong induction that splits
`n` by parity, uses the behaviour of the alternation count under appending a
letter, and closes the odd case with a boundary fact about three consecutive
Thue-Morse letters.

Second, the reduced Parikh vectors realised at a fixed length form an interval
of alternation counts, so the class count is the size of a weighted interval
determined by the two extremes. Shifting the length from `4n` to `4n+2` moves
that interval by a controlled amount, and the resulting difference of the two
counts reduces to the difference of the two extremes modulo two. Combining with
the first step gives the stated dichotomy.

## Falsifier

An `n` with `0 < n` at which the absolute difference is neither zero nor one, or
at which it disagrees with the Thue-Morse condition, would contradict the
theorem about the defined class count.

## Evidence

- Module: `D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.lean`.
- Theorem: `reducedAbelianComplexity_even_difference`.
- Supporting public result: `alternation_extrema_parity`.
- The class count is the frozen `R` of `ThueMorseReducedAbelianOdd`, unchanged.
- No finite cutoff appears in either public statement.

## Triage

`theorem`. Only the displayed absolute difference is settled. The sign of
`rho(4n+2) - rho(4n)` when the difference is nonzero, a recursion for `rho(4n)`,
the full recursion for `rho(n)`, and non-k-automaticity of the printed sequence
all remain open and are untouched here.

## ASSUMED-UNVERIFIED

The identification of the paper's `rho` with this repository's `R` rests on a
human reading of the printed definition together with term-by-term agreement
with the paper's own printed sequence over a bounded window. It is not a machine
proof of that identification. First-publication priority is not established, and
no search for a later resolution of equation (11) was performed.
