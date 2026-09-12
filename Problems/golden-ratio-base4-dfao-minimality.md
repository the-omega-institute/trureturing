---
slug: golden-ratio-base4-dfao-minimality
bibkey: barnoffbrightshallit2024using
doi: 10.48550/arXiv.2405.02727
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

- The automaton layer is partly frozen as of 2026-09-01 and 2026-09-12:
  `D5/S0/Automata/DFAOStateLowerBound` carries `DFAO` over Mathlib's `DFA`,
  `evalOutput`, `CorrectOn` for an explicitly declared domain, the
  `DistinguishingFamily` certificate and its state lower bound, and
  `D5/S0/Automata/DistinguishingFamilyCardinalityBound` carries the upper bound on
  that certificate. Still absent: the sparse powers language itself, the target
  digit function, Myhill-Nerode equivalence for the output setting, and any
  automaton minimization theorem.
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
3. **Closed, 2026-09-12.** Seeking 22 pairwise distinguishable residual
   configurations cannot work, and the obstruction belongs to the certificate
   method rather than to a shortage of compute. On this sparse language almost
   every prefix admits exactly one legal continuation, such prefixes can only be
   separated from each other by that one shared continuation, and the base-4
   output alphabet then caps the family at four. `D5/S0/Automata/DistinguishingFamilyCardinalityBound`
   states this as a theorem: a `DistinguishingFamily` whose prefixes each admit a
   unique legal continuation has at most `Fintype.card Output` indices, so the
   bound extracted through `state_lower_bound_of_distinguishing_family` can never
   exceed the output alphabet on such a domain. The exact counts are under
   Evidence. Do not spend a seat on this step.
4. Therefore the surviving route is the paper's own: reproduce the incomplete-data
   SAT model incrementally and require a DRAT/LRAT UNSAT certificate for 21 states
   plus a theorem connecting the finite constraint family to all powers. A cheaper
   certificate would need the sparseness itself to be broken, for example by
   certifying a larger domain than the powers, which changes the question the paper
   asked and must not be done silently.
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
2. **Done, 2026-09-12; result is the closure of Route step 3.** The `i`th base-4
   digit of phi was computed as `(4^i + isqrt(5 * 16^i)) / 2 mod 4` and the
   Zeckendorf words by greedy Fibonacci, each checked to contain no `11` and to
   invert back to `4^a`. The full residual conflict graph was built over every
   prefix of every language word, joining two prefixes when some common
   continuation lands both in the language with different output digits, and an
   exact maximum clique was computed per connected component by Bron-Kerbosch with
   pivoting. The maximum distinguishing family is **4** in every configuration
   measured: powers up to `a = 120`, `240` and `360`, in both
   most-significant-first and least-significant-first digit order, over 179, 163,
   414, 311 and 622 components respectively. The mechanism is visible in the
   counts: of the 19,828 distinct prefixes at `a <= 120`, **19,637 have exactly one
   continuation**, and no two of the 121 words share a 16-digit tail.
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

`window`. The problem has a finite 22-state target, but one of its two
certificate-shaped attacks is now closed by theorem and measurement, and the
repository still lacks the SAT proof layer that the remaining attack needs. The
automata layer is no longer entirely absent: `D5/S0/Automata/DFAOStateLowerBound`
supplies the output automaton, its correctness predicate on a declared domain, and
the distinguishing-family lower bound, and `D5/S0/Automata/DistinguishingFamilyCardinalityBound`
supplies the matching upper bound on what that certificate can ever prove. The
paper already reports severe scaling on the route that remains.

## ASSUMED-UNVERIFIED

- The paper's base-4 Walnut automaton has exactly 22 reachable states under the
  conventions relevant to the question.
- Exact digit generation through a large finite range will expose all faulty
  small DFAO candidates quickly enough for incremental SAT.
- Whether the fixed base-4 minimality question was resolved after arXiv v1 is
  unverified; novelty of any certificate construction is unassessed.
- The maximum distinguishing family was measured on the finite samples listed under
  Evidence, not proved for every `a`. The theorem that explains those numbers is
  proved, but its rigidity hypothesis is stated about a family's own prefixes and is
  not derived here from properties of the Zeckendorf encodings of the powers.
