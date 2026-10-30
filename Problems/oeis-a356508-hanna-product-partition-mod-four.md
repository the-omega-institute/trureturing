---
slug: oeis-a356508-hanna-product-partition-mod-four
bibkey: hanna2022a356508
doi: null
url: https://oeis.org/A356508
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.result
---

# Hanna's OEIS A356508 product-partition congruence

## Problem

P. D. Hanna, OEIS A356508, created 11 August 2022. The NAME field states:

> G.f. A(x) satisfies: 2 = Product_{n>=1} (1 + x^n*A(x)) * (1 + x^(n-1)/A(x)).

The COMMENTS field states:

> Conjecture: a(n) == 2 (mod 4) at n = 2*k for all k > 0 that have an odd number of partitions (A052002), otherwise a(n) == 0 (mod 4) when n > 0.

The formal statement uses rational formal power series, takes the product coefficientwise through the finite window needed for each coefficient, and interprets the partition number as `Fintype.card (Nat.Partition k)`. It asserts existence of a solution and the quoted integer and residue properties for every positive coefficient.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| `G.f. A(x) satisfies: 2 = Product_{n>=1} (1 + x^n*A(x)) * (1 + x^(n-1)/A(x))` | `IsGF A` over `PowerSeries ℚ`; at degree `m` the product is `Finset.Icc 1 (m + 1)`, and `A⁻¹` is `invOfUnit A 1`. |
| “a(n) == 2 (mod 4) at n = 2*k for all k > 0 that have an odd number of partitions (A052002)” | For `0 < n`, an integer `z` equal to `coeff n A` satisfies `z ≡ 2 [ZMOD 4]` whenever some `k > 0` has `n = 2 * k` and `Odd (Fintype.card (Nat.Partition k))`. |
| “otherwise a(n) == 0 (mod 4) when n > 0” | For the same positive `n`, if no such `k` exists then `z ≡ 0 [ZMOD 4]`. |
| “The terms are integers.” | The claim supplies an integer `z` equal to every positive coefficient. |

## Motivation

The conjecture gives a residue description for the coefficients of the generating function specified by the entry. The settlement identifies the unique rational solution and makes the parity of the ordinary partition numbers the only input to the modulo-four coefficient formula.

## Gap

Preregistration issue [#18879](https://github.com/the-omega-institute/trureturing/issues/18879) records the verbatim entry text, complete quantifiers, Lean conventions, the finite experiment, and the literature screen. The entry contains the conjecture without a cited proof. The result is admitted as an external open-problem resolution and is proved by the kernel-checked theorem `D5.S1.Recurrence.Invariants.HannaProductPartitionModFour.result`.

## Route

Coefficientwise agreement gives a contraction: the coefficient of degree `m` in the product depends only on coefficients below degree `m`. Iterating the resulting fixed-point operator constructs a unique solution with constant coefficient one and integer coefficients. In `ZMod 4`, the identity `A + A⁻¹ = 2` modulo four reduces every paired factor to `(1 + x^n)^2`. The inverse of this product modulo two is the partition series in `x^2`, so the coefficient at a positive even index is twice the partition number at half the index and the coefficient at an odd index is zero modulo four.

## Falsifier

A positive index with a nonintegral coefficient, a residue different from `2 * p(n/2)` modulo four at an even index, or a nonzero residue at an odd index would contradict the result. A failure of the coefficientwise finite-window interpretation would also invalidate the encoding of the source equation.

## Evidence

The Lean module and its Scribe mirror are `D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.lean` and `Blueprint/D5/S1/Recurrence/Invariants/HannaProductPartitionModFour.scribe.cs`. The public settlement is `result : claim`, whose kernel axiom closure is `{propext, Classical.choice, Quot.sound}`. Its proof reuses the frozen coefficient-agreement, inverse, and partition-product declarations named in the module header.

The independent experiment is in `the-omega-institute/trureturing-experiments/docs/reports/oeis-a356508-hanna-product-partition-mod4` at commit `b545d0b3f4226d80274b80c06cf01c1153c12957`. The command `python3 check.py 120 b356508.txt` exited `0` with `RESULT PASS`; `check.py` has SHA-256 `00c00982ce21ca8c40c9e9c216f48bffc4a79dbf590b1eadecde697c815f0ab3`. This finite check supports the universal Lean conclusion and does not replace it.

## Triage

This is a Tier 1 OEIS conjecture. The settlement theorem is classified `proof_shape: bind-only` under the repository's inlining rule, with `admission_basis: open-problem-resolution (#18879; Proved)`.

### What the settlement shows

- **Proved in this module:** the coefficientwise product equation has a rational solution, every positive coefficient is an integer, and the conjectured modulo-four alternatives hold for every positive index.
- **Proved mechanism:** coefficient contraction constructs the unique source solution; modulo four, the paired factors collapse to `(1 + x^n)^2`; the reciprocal partition identity then gives the coefficient formula.
- **Extension:** the same coefficient formula applies uniformly at every positive index and identifies the unique solution under the stated rational and nonzero-constant-coefficient hypotheses.
- **Computed:** the cited experiment checks the defining product and the first 120 coefficients.
- **Open:** residues modulo eight, a replacement of the constant `2` by a general scalar, and Jacobi triple-product or asymptotic questions are outside this settlement.

## ASSUMED-UNVERIFIED

The literature screen checked the OEIS entry, cited and related papers, the repository's prior formal-conjecture corpora, and the sources recorded in issue #18879; it did not establish worldwide absence of an unpublished or unindexed proof. The correspondence between the published prose and the Lean encoding is established by the source quotation and the Scribe formula, while the kernel verifies only the formal proposition and its standard axiom closure.
