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

The concrete target was the base-4 phi instance: determine whether the paper's
22-state Walnut DFAO is minimal among machines correct on the Zeckendorf
encodings of all `4^i`, ignoring leading zeroes and obeying the
Zeckendorf/Ostrowski validity rules. The target is refuted below by a
21-live-state partial DFAO satisfying these conventions and agreeing on every
admissible encoding.

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
- The actual 22-state Walnut transition/output table is imported and checked by
  the delivered module's finite certificates and structural induction.
- No SAT encoding is needed for the refutation: a concrete 21-live-state
  witness is enough.
- Correctness on every `4^i` follows from the stronger theorem for every valid
  Zeckendorf encoding, rather than from a finite digit dictionary.

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
4. **Closed, 2026-09-29.** The delivered `reducedBase4AdmissibleDFAO` has 21
   live states. `legal_transition_certificate` checks all finite table cases;
   `reduced_run_is_lift_compatible` lifts the resulting run by induction on
   every valid word; and `reduced_obeys_zeckendorf_ostrowski_rules` checks the
   partial-machine convention. `paper_base4_golden_ratio_dfao_is_not_minimal`
   packages the exact counterexample.
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

1. The 22-state table and the 21-live-state reduction are retained in the
   Evidence receipt and checked by the module's finite table certificates.
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
3. No SAT lower-bound search is required after the explicit counterexample.

The exact refutation is a universal structural proof, not a finite-prefix
candidate: every legal transition is checked and the run compatibility theorem
inducts over arbitrary valid words.

## Resolution

`D5/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.paper_base4_golden_ratio_dfao_is_not_minimal`
constructs a 21-live-state partial DFAO. It agrees with the literal 22-state
paper table on every valid Zeckendorf encoding, ignores leading zeroes, and
obeys the rule that a second consecutive one enters the implicit dead state.
Therefore the paper's 22-state minimality claim for the fixed base-4 instance
is false. The broader general minimality and uniqueness questions remain open.

## Triage

`theorem`; the fixed base-4 minimality claim is refuted by the universal
21-live-state witness above. The broader paper question about minimality and
uniqueness in general is not settled.

## ASSUMED-UNVERIFIED

- Whether the 2026 journal follow-up independently reports the same 21-state
  reduction is unverified; no priority claim is made.
- The maximum distinguishing family was measured on the finite samples listed under
  Evidence, not proved for every `a`. The theorem that explains those numbers is
  proved, but its rigidity hypothesis is stated about a family's own prefixes and is
  not derived here from properties of the Zeckendorf encodings of the powers.
