---
slug: chaudhary-khandelwal-2026-apery-spectrum-kb
bibkey: chaudharykhandelwal2026aperyspectrum
doi: 10.48550/arXiv.2611.33046
url: https://arxiv.org/abs/2611.33046v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/NumericalSemigroups/ChaudharyKhandelwalAperySpectrum.family_spectrum
---

# The Apéry spectrum at modulus kb for the family {0, a, b, kb}

## Problem

Chaudhary and Khandelwal ask in [§8(2), p. 21](https://arxiv.org/pdf/2611.33046v1#page=21):

> Other families. The spectrum of {0, a, b, 2b} is governed by the three-distance theorem (Section 5). Compute the spectrum at the modulus d of other complete-intersection families, such as {0, a, b, kb} with 0 < a < b coprime and k ≥ 3; for k ≥ 3, b is not a modulus, since b ∉ S₂.

The named family runs over positive coprime natural numbers a < b and natural k ≥ 3.
The maximum d = kb belongs to both generated monoids and is the modulus for this computation.

## Motivation

The spectrum counts the nonempty intervals contained in each source hole set,
then sorts the positive counts in weakly decreasing order with repetitions retained. An explicit evaluator computes
every entry from a, b and k.

## Gap

The open question names this entire family. It requires an evaluator for each
admissible triple, including the multiplicities and the zero tail.

## Route

At each residue, a unique point of Fin(b) × Fin(k) determines the Apéry
minimum of each additive closure. Reducing the first coefficient modulo b
and then the second modulo k supplies the nonnegative carries in the
leastness proof. The two maximal thresholds occur at the upper corner.
Scanning positive residues and summing run lengths counts every nonempty
interval in a hole set at its right endpoint. Sorting the two lists of
positive counts gives the source spectrum at each index.

## Falsifier

A second rectangle point at the same right residue, a smaller element of
either monoid in the corresponding residue, or any disagreement between the
evaluator and the source spectrum at an admissible triple would contradict
the respective Lean theorem.

## Evidence

- Simultaneous Apéry minima in the actual generated additive closures.
  D5/S3/Arith/NumericalSemigroups/ChaudharyKhandelwalAperySpectrum.residue_witness
- Pointwise equality, weakly decreasing order, exact positive support and
  the two-list count formula.
  D5/S3/Arith/NumericalSemigroups/ChaudharyKhandelwalAperySpectrum.family_spectrum
- The indexed spectrum agrees with the paper's one-based spectrum by
  sending index n to n + 1.

## Triage

`theorem`. The computation covers the full explicit family {0, a, b, kb}.

### What the settlement shows

The rectangle carries determine the two least representatives, and the
sum of the threshold maxima is b + k − 2. Each positive block-count list
strictly decreases. Together these facts give exactly b + k − 3 positive
entries, at most two occurrences of any value in the finite list, and zero
at every later index. These conclusions follow from
`D5/S3/Arith/NumericalSemigroups/ChaudharyKhandelwalAperySpectrum.family_spectrum`.

## ASSUMED-UNVERIFIED

Other complete-intersection families in §8(2) remain outside this
settlement. The optimized floor and gap method and the complete-intersection
and Cohen–Macaulay assertions are outside the Lean result.
