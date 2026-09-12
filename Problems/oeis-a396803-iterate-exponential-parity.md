---
slug: oeis-a396803-iterate-exponential-parity
bibkey: hanna2026a396family
doi: null
url: https://oeis.org/A396803
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateExponentialParity
---

# Parity of the A396803 iterated-exponential coefficients

## Problem

Paul D. Hanna's NAME and every conjecture COMMENT, quoted verbatim from the
entry snapshot:

```text
%N A396803 E.g.f. satisfies A(x) = x*exp( A^3(x) ).
%C A396803 Conjecture: a(n) is odd iff n is odd for n >= 1.
%C A396803 Conjecture: a(n) == [1,2,0] repeating (mod 3) for n >= 1.
%A A396803 Paul D. Hanna, Jun 08 2026
```

In this entry `A^3(x)` denotes the 3-fold COMPOSITIONAL ITERATE of `A`, not
the 3-th power; the entry's formula field states that convention explicitly.
The offset is 1 and the first terms are 1, 2, 21, 472, 17165, 885696, 60160723.

This lane settles ONLY the parity conjecture. The remaining
conjecture quoted above,
on residues modulo three,
is NOT proved, is not claimed,
and does not appear in the module in any form.

## Motivation

The candidate comes from the repository's own triage notes
`Library/Words/oeis2026triage0909.md` and `oeis2026triage0911b.md`. The target is
a universal statement over all positive indices, not a finite check. The proved
theorem is uniform in the iterate count, so one argument covers this entry
together with its siblings A396805, A396806.

## Gap

The entry snapshot carries no proof and no reference to one. The repository
already contained the k = 4 member of this family
(`D5/S1/Recurrence/Residue/QuarticEGFModFour`, a modulo-four congruence), and its
supporting EGF composition calculus, but nothing about parity and nothing for a
general iterate count: its `step` operator hardcodes the fourth iterate. The
formal gap was a characterisation, modulo two, of the operator
`A ↦ X * exp(A^{[k]})` for every k.

## Route

Coefficients are integral EGF coefficients, `eCoeff f n = n! * coeff n f`.

1. The k-general construction mirrors the frozen quartic one with the iterate
   count released as a parameter: `stepK`, its map/contraction/coefficient
   lemmas, the stage sequence `approximationK`, the natural-number sequence
   `aK k`, and the series `AK k`. `A_equation` proves
   `constantCoeff (AK k) = 0 ∧ AK k = X * (exp ℚ).subst (iterateComp (AK k) k)`,
   which is the entry's defining equation, and `fixed_unique` proves any series
   satisfying it is that one. Together these make `aK k` the entry's sequence
   rather than an unrelated recurrence.
2. Write `F = X * exp X`, whose integral EGF coefficients are exactly `n`. The
   parity claim `a(n) ≡ n (mod 2)` is therefore the statement that the fixed
   point reduces to `F` modulo two.
3. The escape content is the modulo-two evaluation of
   `expLinear = composition (fun _ => 1) linear`, the integral EGF coefficients of
   `exp(X exp X)`: its closed form is `∑_k C(m,k) * k^(m-k)`, and modulo two every
   term with `k < m` collapses to `C(m,k) * k`, the `k = m` term is one, and the
   odd-index binomial sum is `2^(m-1)`, giving `expLinear m ≡ 1 - m (mod 2)`. In
   particular every even-indexed coefficient is odd.
4. `iterate` of the reduced identity sequence is 2-periodic modulo two, because
   the frozen `square_mod_two` gives `F ∘ F ≡ X`. Hence `stepK k` fixes the
   identity class modulo two for EVERY k: for even k the inner iterate is the
   composition identity; for odd k it is the identity sequence, and the leading
   factor `n + 1` disposes of odd `n` while step 3 disposes of even `n`.
5. Induction over the approximation stages carries the congruence to the fixed
   point, giving `parity_mod_two` and then `odd_iff_odd`; `parity_iterate_three` is its
   specialization at k = 3.

## Falsifier

An index `n ≥ 1` with `aK 3 n` odd while `n` is even, or even while `n` is odd,
falsifies the theorem. A second series satisfying the same defining equation with
the same vanishing constant coefficient would falsify `fixed_unique`.

## Evidence

- Module: `D5/S1/Recurrence/Residue/IterateExponentialParity.lean`.
- Resolution theorem: `parity_iterate_three`, a specialization of `odd_iff_odd`.
- Companions: `A_equation`, `fixed_unique`, `odd_iff_odd`, and the sibling
  specializations.
- Axioms: every public theorem reports `[propext, Classical.choice, Quot.sound]`.
- The module's own `aK 3` was evaluated by the Lean kernel in a scratch file and
  returned 1, 2, 21, 472, 17165, 885696, 60160723 at indices 1 through 7, matching the published terms. The
  same check at k = 4 returned 1, 2, 27, 820, 41005, 2933046, which agrees with the
  independently frozen `QuarticEGFFixedPoint` sequence for A396804.
- Exact rational computation outside Lean reproduced the published terms for
  k = 3, 5 and 6, found every coefficient integral through index 12, and found the
  parity statement to hold with zero violations there; it also holds for k = 1, 2,
  7 and 8, which is why the proved theorem is stated for every k.

## Triage

`theorem`. One universal conjecture of this entry is settled, for a sequence
proved to satisfy the entry's defining equation. The residue
conjecture remains open.

## ASSUMED-UNVERIFIED

The entry text is a snapshot; the implementation seats had no network and did not
retrieve OEIS or search the literature, so no literature completeness or
first-publication priority is claimed. The computations recorded under Evidence
ran outside the Lean kernel except for the stated `aK` evaluation; the proved
content is exactly the public theorems. Identification of this entry's sequence
with `aK 3` rests on `A_equation` together with `fixed_unique`, not on numerical
agreement.
