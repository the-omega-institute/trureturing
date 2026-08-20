---
slug: base-phi-negative-prefix-trident
bibkey: dekking2023structure
arxiv_id: 2305.08349
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

- Frozen digits are nonnegative Fibonacci-index coordinates; `beta^-(N)` uses
  negative powers of phi and is not represented.
- No theorem currently converts a canonical Zeckendorf expansion to the
  two-sided base-phi expansion.
- The paper's morphisms `f, g, h`, the parameterized sequence families
  `V_F, V_G, V_H`, and the union-of-three data are absent.
- Existing return-word theorems concern factors of the frozen golden word; it
  remains to prove that negative-prefix cylinders land in those exact subshifts.

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

## Triage

`theorem`. The missing two-sided conversion is substantial, but the repository
already owns precisely the normalization, mechanical-word, Beatty, and
return-gap ingredients suggested by the conjecture's shape.

## ASSUMED-UNVERIFIED

- The paper's phrase "union of three" has a unique intended formal
  parameterization and does not require extra overlap/multiplicity conventions.
- A bounded-state transducer from WDigits to every fixed negative prefix exists
  in a form compatible with current definitions.
- The frozen golden return-word theorems apply after a finite shift/intercept
  change; this is the main bridge to prove.
- Whether the conjecture was resolved after arXiv v1 is unverified, and any
  novelty of intermediate bridge theorems is unassessed.
