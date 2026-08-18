---
slug: golden-ratio-base4-dfao-minimality
bibkey: barnoffbrightshallit2024using
arxiv_id: 2405.02727
triage: window
motivation_gids:
  - D5/S0/Conventions/WDigits
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S1/Words/ZeckendorfOrder
  - D5/S1/Words/ZeckendorfBeattyBridge
  - D5/S1/Depth/GoldenContinuedFraction
  - D5/S1/Scale/Fibonacci
---

# Minimality of the base-4 golden-ratio DFAO

## Problem

The paper constructs a DFAO which, on the Zeckendorf representation of `q = b^i`,
outputs the `i`th base-`b` digit of the golden ratio. The full Walnut automaton
is minimal on all valid inputs, but only powers of `b` matter for digit
extraction.

Quoted from arXiv:2405.02727v1:

> “Could it be that there are even smaller automata that answer correctly on
> inputs of the form \(b^i\) (but might give a different answer for other
> inputs)?”

> “We do not know the answer to this question, in general.”

The concrete target is the unresolved base-4 phi instance: prove that the
paper's 22-state Walnut DFAO is minimal among DFAOs which are correct on the
Zeckendorf encodings of all `4^i`, ignore leading zeroes, and obey the
Zeckendorf/Ostrowski validity rules. Equivalently, prove that no such DFAO with
at most 21 states exists.

The paper also says:

> “It is conceivable that the automata produced by our method are indeed minimal
> and unique in general, and we leave this as an open question.”

Minimality of the fixed base-4 instance is narrower and mechanically
falsifiable; uniqueness should remain a separate target.

The paper states the difficulty:

> “The question is likely difficult; in terms of computational complexity, it is
> a special case of a problem known to be NP-hard, namely, the problem of
> inferring a minimal DFAO from incomplete data.”

> “For this reason, \(\varphi\) in base 4 ... encountered prohibitively long
> solving times before the required number of states (22 states ...) could be
> reached, preventing the minimality of the Walnut solutions from being
> determined.”

> “For \(\varphi\) in base 4, it took over 25 hours for the 78'th digit set to
> be declared UNSAT at 13 states...”

The paper explains that both the digit set needed for a candidate and the
representation length of each digit position can be arbitrarily large.

## Motivation

- The input language is exactly the frozen Zeckendorf system; leading-zero
  invariance and the no-adjacent-ones rule can be stated over `WDigits` and
  normalization.
- `GoldenContinuedFraction` and Fibonacci scale give the golden/Ostrowski
  arithmetic that underlies the digit extractor.
- `ZeckendorfOrder` and the Beatty bridge may support exact generation of
  constrained positive and negative examples without floating-point phi.
- The remaining task is automata-theoretic minimality on a sparse input
  language, so the connection is real but one layer farther from existing
  machinery than the other five candidates.

## Gap

- No DFA/DFAO, run semantics, sparse powers language, Myhill-Nerode
  equivalence, or automaton minimization theorem is frozen.
- The actual 22-state Walnut transition/output table must be imported from the
  paper artifact and independently checked.
- No SAT encoding, UNSAT proof checker, or certificate format exists in the
  repository.
- Correctness on every `4^i` is an infinite sparse-language property; matching a
  finite digit dictionary is not enough.

## Route

1. Define the sparse language `L_4 = {zeckendorf(4^i) | i >= 0}` and the target
   output digit function exactly.
2. Verify the 22-state machine on `L_4` using the paper's arithmetic
   construction, separately from minimality.
3. Seek 22 pairwise distinguishable residual configurations: for each pair of
   proposed equivalence classes, exhibit a continuation compatible with some
   power input that forces different output. This would give a checkable
   Myhill-Nerode-style lower-bound certificate without solving a monolithic SAT
   instance.
4. If sparse continuations do not support such a certificate, reproduce the
   paper's incomplete-data SAT model incrementally and require a DRAT/LRAT UNSAT
   certificate for 21 states plus a theorem connecting the finite constraint
   family to all powers.
5. Treat uniqueness only after minimality; multiple machines agreeing on all
   observed digits are not proof of non-uniqueness.

## Falsifier

An explicit DFAO with at most 21 states satisfying both conventions and proved
correct for every Zeckendorf encoding of `4^i` falsifies 22-state minimality. A
finite-prefix match is only a candidate counterexample, not a falsifier.

For a proposed distinguishability certificate, one pair of purported residual
classes that is actually equivalent on all legal power continuations invalidates
that certificate.

## Evidence

1. Transcribe the 22-state table and verify its outputs against exact integer
   arithmetic for the first 100,000 base-4 digits of phi.
2. Generate sparse-input prefix trees for increasing `i`, minimize the finite
   labeled trees, and track stabilization of the number and signatures of
   residual classes.
3. Run incremental SAT for 13 through 21 states, preserving per-bound wall time,
   dictionary extent, candidate automata, and a proof certificate for every
   UNSAT result.
4. Whenever SAT finds a smaller candidate, use exact arithmetic to locate its
   first wrong digit and feed that witness back as a new constraint.

The first meaningful result is either a reproducible 21-state-or-smaller
candidate with its first failure, or a mechanically checked UNSAT certificate at
a stated finite constraint level. Neither alone proves the infinite minimality
theorem.

## Triage

`window`. The problem has a finite 22-state target and certificate-shaped
attacks, but the repository lacks the entire automata/SAT proof layer and the
paper already reports severe scaling.

## ASSUMED-UNVERIFIED

- The paper's base-4 Walnut automaton has exactly 22 reachable states under the
  conventions relevant to the question.
- A finite distinguishability basis exists for the sparse powers-only language.
- Exact digit generation through a large finite range will expose all faulty
  small DFAO candidates quickly enough for incremental SAT.
- Whether the fixed base-4 minimality question was resolved after arXiv v1 is
  unverified; novelty of any certificate construction is unassessed.
