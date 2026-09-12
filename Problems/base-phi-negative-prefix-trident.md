---
slug: base-phi-negative-prefix-trident
bibkey: dekking2023structure
doi: 10.48550/arXiv.2305.08349
triage: theorem
motivation_gids:
  - D5/S0/Conventions/WDigits
  - D5/S1/Words/ZeckendorfOrder
  - D5/S1/Words/ZeckendorfBeattyBridge
  - D5/S1/Words/GoldenMechanicalWord
  - D5/S1/Words/GoldenSubstFixed
  - D5/S1/Words/Complexity/MechanicalSubshiftIntercept
  - D5/S1/Words/ReturnWords/GoldenReturnWords
  - D5/S1/Words/ReturnWords/GoldenReturnWordsExact
  - D5/S1/Words/ReturnWords/GoldenOccurrenceGaps
  - D5/S1/Words/ReturnWords/GoldenReturnItinerary
  - D5/S1/Deficit/ZeckendorfDisplacementReading
---

# Classify negative base-phi prefix occurrence sequences

## Problem

Write the canonical base-phi expansion as `beta(N) = beta^+(N) . beta^-(N)`, and,
for a word `w` of length `m`, let `R_{.w}` be the increasing sequence of natural
numbers `N` whose first `m` negative-position digits are `w`, that is
`d_{-1}...d_{-m}(N) = w`. The paper defines three families `V_F, V_G, V_H`
through first-difference words `x_F, x_G, x_H` arising from three Sturmian
morphisms.

The conjecture, quoted from arXiv:2305.08349v1:

> “Let \(\beta(N)=\beta^+(N)\cdot\beta^-(N)\) be the base phi expansion of the
> number \(N\). Let \(w\) be a word of length \(m\). Let \(R_{\cdot w}\)
> be the sequence of occurrences of numbers \(N\) such that the first \(m\)
> digits of \(\beta^-(N)\) are equal to \(w\), i.e.,
> \(d_{-1}\ldots d_{-m}(N)=w\). Then there exist two Lucas numbers \(a\) and
> \(b\) such that either \(R_{\cdot w}=V_F\), or \(R_{\cdot w}=V_G\), or
> \(R_{\cdot w}=V_H\). A second possibility is that \(R_{\cdot w}\) is a
> union of three of such sequences.”

Proposed formal target: port the paper's parameterized definitions faithfully,
then prove that every admissible negative prefix cylinder has an occurrence set
represented by one trident component `V_F`, `V_G`, or `V_H`, or a union of three
such components with Lucas parameters. Do not weaken this to mere eventual
periodicity or occurrence.

The paper states the obstruction:

> “However, this does not work. The reason is that the \(\beta^-(N)\) words do
> not occur in lexicographical order, in contrast with the \(\beta^+(N)\)
> words.”

It adds that some occurrence sequences are Lucas-Wythoff and some are not,
although they remain close to that form. It exhibits the first `V_G`, the first
`V_H`, and a three-component case, but not the general classification.

## Motivation

- The positive Zeckendorf side already has numerical lexicographic order and an
  exact Beatty/mechanical least-digit bridge.
- The return-word layer is closer than a generic Sturmian fact: it already turns
  golden factor cylinders into exact return itineraries and finite adjacent-gap
  spectra.
- The conjectural `V_F`/`V_G`/`V_H` alternatives are classifications by
  first-difference words. A plausible bridge is therefore: negative prefix
  cylinder, then a finite-state transducer over canonical Zeckendorf digits,
  then a factor/return itinerary in one of three shifted golden subshifts, then
  an occurrence-gap sequence.
- `ZeckendorfDisplacementReading` supplies an exact digit-upshift/Beatty
  identity that may convert transducer states into Lucas-affine occurrence
  formulas.

## Gap

- The two-sided base-phi expansion is represented: `BasePhiNegative` carries
  `basePhiValue`, `BasePhiNegativeExpansion`, `negativeDigit`,
  `reachesNegativeDepth`, `NegativePrefixOccurs` and `occurrenceSet`, and
  `BasePhiCanonicalExpansion` proves `basePhiExpansion_existsUnique` and
  `canonical_two_sided_digits_unique`.
- A partial Zeckendorf bridge exists, and it is conditional and one-sided:
  `BasePhiCarryTransducer` proves `carrySkipRun_zeckendorf` (the carry-skip
  run's positive component, unconditional), `mem_rawToZeckendorf_iff` (under
  `CanonicalRaw`) and `nonnegative_digit_iff_mem_zeckendorf_of_realizes`, whose
  hypothesis is `realizes : forall N, CarrySkipRealizes expansion N` and whose
  conclusion covers only nonnegative exponents. **The obligation stands**: no
  theorem yet converts a canonical Zeckendorf expansion to the two-sided
  base-phi expansion without that hypothesis.
- The three families are present as first-difference words: `GapFamily`,
  `fibonacciGapLetter`, `familyLetter` (`F`, `G = bF`, `H = aF`),
  `gapSequence`, `vForFamily`, `LucasPair`, `prefixMultiplicity`,
  `CoreLucasWitness`. The paper's substitutions `f, g, h` themselves are not
  formalized; the families are characterized by their first-difference words
  instead, which is the paper's own equivalent description.
- A six-state prefix machine exists: `FrontierPhase`
  (`F0o, F1o, F0e, G1e, G0o, H0e`), its ten transitions
  `FrontierPhaseTransition`, the base cases `PrefixPhaseMachineFor`
  (`[0]` to `<F0o,4,3>`, `[1]` to `<F1o,7,4>`), and `FrontierReturnWord`.
- The reading question is settled by `BasePhiNegativePrefixPaddedReading`:
  `NegativePrefixOccurs` carries the extra conjunct
  `reachesNegativeDepth expansion N w.length`, which is not the paper's reading.
  Under that conjunct the paper's own Proposition 7.8 d) identity
  `R_{.01} = R_{.010}` fails, with symmetric difference exactly `{2, 3, 4}`;
  under the zero-padded reading it holds and is a corollary of canonicality.
- What remains open is the classification itself. Existing return-word theorems
  concern factors of the frozen golden word; it remains to prove that
  negative-prefix cylinders land in those exact subshifts.

## Route

1. Port the two-sided base-phi expansion and prove value/uniqueness by clearing
   negative powers with a suitable phi power and invoking `GoldenInt`/WDigits
   normalization.
2. Construct a finite carry transducer from a Zeckendorf word to the first `m`
   digits of `beta^-`; its state should be a bounded conjugate/deficit residue
   because the negative tail is contractive.
3. Identify the output cylinder's return itinerary with `x_F`, `x_G`, `x_H`, or
   a three-state interleaving. Use frozen return-word and occurrence-gap results
   after this identification, not before it.
4. Prove Lucas parameters by induction/desubstitution on `w`; use the frozen
   Beatty displacement reading to close the affine occurrence formula.
5. Start with a declaration-ready restricted theorem for prefixes ending in a
   state whose transducer is a single `V_F` component, then generalize to the
   trident.

## Falsifier

An admissible word `w` for which the exact occurrence sequence has a
first-difference factor impossible in all three of `x_F`, `x_G`, `x_H`, even
after testing every Lucas parameter and every allowed three-component
interleaving, falsifies the conjecture.

A finite prefix alone cannot refute equality of infinite sequences unless it
contradicts a necessary invariant. Use invariants such as allowed gap alphabet,
factor complexity, return-word count, and Lucas congruence classes; report the
first violating index and exact base-phi expansion.

## Evidence

For all admissible `w` of length at most 14:

1. compute exact two-sided base-phi expansions for `1 <= N <= 2,000,000` using
   integer pairs in `Z[phi]`, not floating point;
2. extract `R_{.w}` and its first differences;
3. infer a candidate `F`/`G`/`H` state and Lucas pair from a training prefix;
4. verify on a disjoint tail and check necessary return-word/factor invariants;
5. emit the smallest unresolved or contradictory `w` with a reproducible
   integer-coordinate trace.

The first Evidence goal is to validate the finite transducer and discover its
states, not to certify the infinite conjecture from samples.

Steps 1 and 2 of the protocol above have been run, and step 3 only in the
degenerate form of classifying every word directly rather than inferring from a
training prefix. Step 4 -- verification on a disjoint tail and the
return-word/factor invariant checks -- and step 5 have NOT been run.

The reproducible part of this is already in the repository:
`Evidence/D5/S1/Words/BasePhiNegativePrefixTrident.result.json` records a scan
with `limit 2000000`, `max_prefix 14`, `min_exponent_guard -96`, and
`method: exact integer-pair arithmetic in Z[phi]`, classifying
`single_family 986`, `three_family 1595`, `unresolved_count 0`. That artifact
also records `01` with 633438 occurrences against `010` with 633435 -- a
difference of exactly 3, which is the `{2, 3, 4}` that
`occurrenceSet_prefix01_symmDiff_prefix010` now proves, and which that artifact
reports as `matched: true` for both words.

`ASSUMED-UNVERIFIED` -- the following were run outside the repository and their
programs are not committed here, so a reader cannot recompute them: an
independent enumeration to `1 <= N <= 4,000,000` over the same 2,581 admissible
words of length at most 14, by two implementations agreeing on `20,000 x 10`
digits; and the selector counts below. The counts that the committed artifact
does cover -- 986 single, 1595 trident, 0 unresolved, and 987 admissible words
at length 14 -- agree with that independent run. What was additionally
measured: window
`1 <= N <= 4,000,000`, all 2,581 admissible `w` of length at most 14, exact
integer arithmetic in `Z[phi]` (two independent implementations agreeing on
`20,000 x 10` digits). Every occurrence set is a single family member or a union
of three, and every step pair is a pair of consecutive Lucas numbers; zero
violations. Leading-component families: `F` 1232, `G` 979, `H` 370. Under the
zero-padded reading the frozen `frontierFamily` selector has zero
counterexamples and `dataFrontierFamily` has 276; under the
`reachesNegativeDepth` reading the two are exactly exchanged. This does not
settle the conjecture; the window is finite.


## Triage

`theorem`. The missing two-sided conversion is substantial, but the repository
already owns precisely the normalization, mechanical-word, Beatty, and
return-gap ingredients suggested by the conjecture's shape.

## ASSUMED-UNVERIFIED

- The paper's phrase "union of three" has a unique intended formal
  parameterization and does not require extra overlap/multiplicity conventions.
- The frozen return-word theorems apply after a finite shift/intercept change;
  this is the main bridge to prove.
- Novelty of the intermediate bridge theorems is unassessed.
- Post-v1 literature status: arXiv:2305.08349 has one version only (15 May
  2023) and was published as Communications in Mathematics 33 (2025) no. 2; a
  search for a later proof of the conjecture returned nothing. That search was
  the orchestrator's own and is not machine-checkable, so the question of
  whether the conjecture was resolved elsewhere stays `ASSUMED-UNVERIFIED`.
- A bounded-state transducer from WDigits to every fixed negative prefix exists
  in a form compatible with current definitions. **This obligation stands**: the
  frozen `FrontierPhase` machine is not it. That machine consumes the prefix
  word and emits a phase with Lucas parameters (`PrefixPhaseMachineFor`,
  `FrontierPhaseTransition`); it does not convert Zeckendorf digits into
  negative-position digits.
- Separately, and not discharging the line above: the `FrontierPhase` machine
  reproduces the measured Lucas step pair `(a, b)` for every admissible `w` of
  length at most 14 over `1 <= N <= 4,000,000`, with zero counterexamples under
  both readings. Whether it does so for every `w` is unverified and is part of
  the conjecture.
- `prefixMultiplicity` (single iff `w` begins with `1`, else a trident) has zero
  counterexamples in the same window; it is not proved for all `w`.
