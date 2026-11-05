---
slug: bala-machine3626-exact-halting-time
bibkey: bala2026machine3626
doi: null
url: https://oeis.org/A393210
triage: theorem
motivation_gids:
  - D5/S0/Computability/BinaryMachine/Machine3626.result
---

# The exact halting time of Wolfram machine 3626

## Problem

Peter Bala, OEIS A393210, conjecture of September 11, 2026, revision 18:

> Conjecture: a(n) = Sum_{d | n} m(d)^2 * phi(d), where m(n) = Sum_{d | n} (-1)^(d+1) * moebius(d) = A069517(n) and phi(n) denotes Euler's totient function A000010(n). Cf. A296306.

The sequence has offset 1. The equivalent conjectural relation in A069517,
revision 31, is the same question, counted once. Here a(n) is the actual
number of transitions of the one-sided two-state two-symbol machine 3626
on every positive natural input n in binary. Its half-tape extends
infinitely leftward, blank zero beyond the most significant bit. The head
starts in state A at the right edge on the least significant bit. Its
rules are A0 → A0L, A1 → B1R, B0 → A1L, B1 → B0R. A simultaneous read,
write, state change and move counts as one transition. Moving right off
the edge terminates the run, and that final transition is counted.
Input zero is excluded. There is no time cap, tape bound or counter width.
Both divisor sums range over positive divisors; the signed Moebius
arithmetic is in the integers.

## Motivation

`D5/S0/Computability/BinaryMachine/Machine3626.result` supplies an actual
first-boundary-crossing trace for every n > 0 whose natural transition
count, cast to the integers, equals the source's signed Moebius/totient
sum. Operational execution is defined independently of the arithmetic
formula. The literal source, published arithmetic prerequisites and
primary machine-number decoder are cited in
`Library/Computability/bala2026machine3626.md`.

## Gap

The external conjecture identifies an operational transition count with
an arithmetic divisor transform. Its exact all-positive-input event is
registered in issue [25808](https://github.com/the-omega-institute/trureturing/issues/25808),
with the unchanged [prospective declaration](https://github.com/the-omega-institute/trureturing/issues/25808#issuecomment-6587694551).
The formal bridge relates a restoring binary block to the arithmetic
transform for all positive inputs.

## Route

A block of k zero bits followed by one and arbitrary higher cells admits
a restoring trace. The recursive step composes two traversals of the
smaller block and three literal transitions, giving T(0) = 1 and
T(k+1) = 2 T(k) + 3, hence T(k) = 4·2^k − 3. Binary recursion finds this
first one for every positive input. Independently, the published
multiplicative Moebius and totient facts reduce the divisor transform to
the same value: the odd factor contributes one and the power of two
contributes 4·2^k − 3. Uniqueness of the initial zero block matches the two
values, yielding the original signed sum and a genuine operational trace.

## Falsifier

Source fidelity would fail if the rule-number decoder, initial head,
implicit blanks or counted boundary-crossing convention differed from the
source. Under the stated semantics, a positive input whose actual first
crossing count differs from the displayed divisor sum would contradict
`D5/S0/Computability/BinaryMachine/Machine3626.result`. Agreement on a
finite set of inputs alone cannot establish this universal claim.

## Evidence

The formal result is
`D5/S0/Computability/BinaryMachine/Machine3626.result`.
Its operational prerequisites are
`D5/S0/Computability/BinaryMachine/Machine3626.block_first_crossing` and
`D5/S0/Computability/BinaryMachine/Machine3626.positive_input_first_crossing`.
The source-equivalence registrations are in
`Reg/D5/S0/Computability/BinaryMachine/Machine3626.lean`; the Blueprint
mirrors the source formula, integer casts and operational conventions.
The primary rule decoder is WolframInstitute/TuringMachine commit
`d23b7bcb741c711ea7b87a76391da1ac150c3bba`, `from_number` in
`TuringMachine/Libs/ndtm_search/src/models.rs`, and initialization/counting
are given by `OneSidedTuringMachineFunctionNative` in
`TuringMachine/Kernel/Functions.wl`. The implementation's maxSteps
parameter is not a hypothesis of the theorem.

## Triage

`theorem`; one source-qualified universal question with the aliases
A393210 and A069517. The source author is Peter Bala; the source tier is 1.

### What the settlement shows

- Proved (`D5/S0/Computability/BinaryMachine/Machine3626.result`): every
  positive binary input has an actual first-crossing trace whose count
  equals the original signed Moebius/totient divisor sum. This proves the
  displayed A393210 conjecture and the equivalent relation in A069517.
- Proved (`D5/S0/Computability/BinaryMachine/Machine3626.block_first_crossing`):
  arbitrary higher Boolean cells can replace the canonical higher binary
  digits once the initial block is k zeros followed by one. The same exact
  count 4·2^k − 3 applies without assumptions on those higher cells; the
  restoring trace is the decisive mechanism.
- Proved (`D5/S0/Computability/BinaryMachine/Machine3626.positive_input_first_crossing`):
  every positive input has such a block. The count is an equality,
  including the final crossing transition, rather than an upper bound.
- Proved (`D5/S0/Computability/BinaryMachine/Machine3626.result`): source
  arguments using precisely the registered conjectural equality may use
  this theorem under the same initialization and counting convention.
  The arithmetic multiplicativity and prime-power prerequisites remain
  reused published results. The citation to A296306 supplies context;
  no additional identity for that sequence is asserted here.
- Open: input zero, other machines, other boundary or counting
  conventions, and any further identities or classifications require
  separate statements and proofs. They are outside this resolution.

## ASSUMED-UNVERIFIED

The bounded known-answer screen covered the exact OEIS identifiers,
repository issues and pull requests, arXiv, Crossref and a Turing-machine
inventory. It found no exact prior answer in the inspected scope; some
broader provider searches were unavailable or incomplete. This is not an
exhaustive absence or priority claim. The theorem resolves the stated
source-qualified event without asserting global novelty.
