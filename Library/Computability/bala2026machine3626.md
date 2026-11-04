---
bibkey: bala2026machine3626
authors: Peter Bala; Sean A. Irvine; Stephen Wolfram
year: 2026
title: "OEIS A393210: halting time for Wolfram machine 3626"
doi: null
url: https://oeis.org/A393210
claim: "Conjecture: a(n) = Sum_{d | n} m(d)^2 * phi(d), where m(n) = Sum_{d | n} (-1)^(d+1) * moebius(d) = A069517(n)."
strata_touched:
  - D5/S0/Computability/BinaryMachine/Machine3626
license: citation-only
triage: anchor
---

# Exact halting time of machine 3626

## Verified locator

https://oeis.org/A393210, revision 18, conjecture line in the comments.
The alias record is https://oeis.org/A069517, revision 31. No DOI is declared.

## Exact question

OEIS A393210, revision 18, records Peter Bala's conjecture of September 11,
2026. The sequence has offset 1 and names Wolfram's two-state two-symbol
machine 3626. A069517, revision 31, records the same question with the two
sides interchanged. These records describe one question.

The source conjecture line in A393210 is:

> Conjecture: a(n) = Sum_{d | n} m(d)^2 * phi(d), where m(n) = Sum_{d | n} (-1)^(d+1) * moebius(d) = A069517(n) and phi(n) denotes Euler's totient function A000010(n). Cf. A296306.

The arithmetic prerequisites are published in A069517: multiplicativity
and the values 2 on positive powers of 2 and 0 on positive powers of odd
primes. The signed sum has value 1 at 1. These are reused arithmetic
facts, not independent discoveries of this formalization.

The registered operational convention is the infinite half-tape to the
left, initially blank beyond the most significant binary digit. The least
significant bit and initial state A are at the right boundary. The rules
are A0 → A0L, A1 → B1R, B0 → A1L, B1 → B0R. Crossing that boundary to the
right terminates the run; the crossing transition counts. Input zero is
excluded. An absent list cell in the formal tape denotes an implicit
blank zero, not a tape bound. No machine step consults an arithmetic
runtime, simulation cutoff or fixed-width counter.

The primary source screen at 2026-11-02T21:50Z found the conjecture lines
unchanged in both raw OEIS records. Prior bounded registration searches
covered repository issues and pull requests, arXiv, Crossref and a Turing
inventory without an exact prior answer. This is not an exhaustive global
absence or priority claim. The primary sources and operational
correspondence remain distinct from the Lean proof.

## Sources

- https://oeis.org/A393210
- https://oeis.org/A069517
- https://www.wolframscience.com/nks/notes-12-8--one-sided-turing-machines/
- https://writings.stephenwolfram.com/2026/01/p-vs-np-and-the-difficulty-of-computation-a-ruliological-approach/
- https://github.com/WolframInstitute/TuringMachine

## Machine encoding

The source implementation at commit
`d23b7bcb741c711ea7b87a76391da1ac150c3bba` is pinned by
`TuringMachine/Libs/ndtm_search/src/models.rs`, function `from_number`.
It takes four base-8 digits in state-major, symbol-reversed order. The
digits of 3626 are 7, 0, 5, 2, corresponding respectively to A1, A0, B1,
B0. A digit v decodes next state as floor(v/4)+1, symbol as
floor(v/2) modulo 2, and right direction iff v is odd. This gives exactly
the four displayed rules, with A = 1 and B = 2.

`TuringMachine/Kernel/Functions.wl`, `OneSidedTuringMachineFunctionNative`,
initializes state 1 at the last digit of the ordinary most-significant-first
input list, with blank symbol 0. It increments the step counter with each
transition and tests for boundary crossing after that transition. Its
implementation parameter maxSteps is a computation bound, not an assumption
or bound in the mathematical conjecture or the Lean theorem.
