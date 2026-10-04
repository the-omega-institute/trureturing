---
slug: psw-all-split-permanental-inequality
bibkey: pan2026permanental
doi: 10.4204/EPTCS.445.17
url: https://arxiv.org/abs/2606.13162v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result
---

# Pan–Skandera–Wang's Permanental Inequality at Every Initial Split

## Problem

Sihong Pan, Mark Skandera and Jiayuan Wang, *Permanental Inequalities and Unit Interval Orders*,
EPTCS 445 (2026), pp. 139–147, DOI 10.4204/EPTCS.445.17, arXiv:2606.13162v1, abstract:

> We also conjecture the inequalities (∗) to hold for all TNN matrices and all h = 1, …, n−1.

Section 1 states:

> We conjecture the inequalities to hold for all totally nonnegative matrices and I = [h].

For every real totally nonnegative matrix `A` of order `n ≥ 2` and every `1 ≤ h ≤ n−1`, the target is

$$
\operatorname{per}(A_{E,E})\operatorname{per}(A_{O,O})
\leq \operatorname{per}(A_{[h],[h]})
\operatorname{per}(A_{[n]\setminus[h],[n]\setminus[h]}).
$$

Here `[h] = {1,…,h}`, and `E` and `O` are the even and odd one-based indices in `[1,n]`.
Total nonnegativity means that every square minor selected in increasing row and column order
has nonnegative determinant. The empty-block permanent is one. Lean's `Fin n` indices start
at zero; `evenIndices n` tests `(i.val + 1) % 2 = 0`, and `prefixIndices n h` tests `i.val < h`.
The source's introductory word “negative” conflicts with its displayed `det(A_{I,J}) ≥ 0`;
the predicate follows that displayed inequality.

## Motivation

`D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result` proves the complete statement.
The existing `D5/S3/Combinatorics/PanSkanderaWangBruhat.result` supplies the rank comparison for
Algorithm 7.5. The supporting modules connect it to a pairing of permanent monomials and
transport the resulting balanced inequality to every initial split.

## Gap

Issue #13069 preregisters the Tier 1 conjecture, its full quantifiers and the identity-padding
route. Its bounded literature screen reports only arXiv v1, an exact-title search returning
this paper, and no proof of the all-split statement. Skandera–Soskin, arXiv:2406.00963, provides
related background without this conclusion. The previously frozen rank comparison addresses
Conjecture 7.8; the all-split permanent inequality is a distinct target.

## Route

The rank-to-chain bridge constructs a finite chain of increasing transpositions. Each
transposition decreases the permutation monomial on a TNN matrix: the difference factors as
a nonnegative product of entries times an increasing two-by-two minor. Injectivity and the
parity image of Algorithm 7.5 give a bijection between the two permanent expansions, proving
the balanced inequality for every order at least four.

For `2h ≤ n`, set `d = n−2h` and pad on the left by `I_d`. The padded matrix has order
`n+d = 2(n−h)` and midpoint `h+d`. Padding preserves TNN and the parity product, while its
midpoint split product equals the original split product. For `2h > n`, simultaneous row
and column reversal preserves TNN and the parity product and sends the split to `n−h`.
The order-two case is equality. These arguments include every order-three split through
padding to order four.

## Falsifier

A counterexample would be a real matrix with every increasing square minor nonnegative and
an initial split whose permanent product is smaller than the parity product. A mismatch
between the literal index sets, the direction of the inequality or the all-order quantifiers
would invalidate fidelity to the source.

## Evidence

The Lean declaration `PSW.result : PSW.claim` is kernel-checked with `propext`,
`Classical.choice` and `Quot.sound`. The definitions use actual submatrix determinants and
Mathlib's `Matrix.permanent`; neither a factorization certificate nor a finite sample replaces
the universally quantified matrix predicate.

## Triage

`theorem`; Tier 1 published conjecture, preregistered in #13069. The settling module uses
`admission_basis: open-problem-resolution`; its proof shape is content. Its public surface
contains only `claim` and `result`. The supporting theorems supply general rank, bijection,
permanent-expansion and padding arguments. Computational utility is `none`: no delivered
declaration is a bounded enumeration, checker, numeric reduction or certified instance.

### What the settlement shows

- **Proved:** the initial-split inequality holds for every real TNN matrix and every admissible
  split, by `D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplits.result`.
- **Proved:** balanced pairing, identity padding and reversal are the decisive mechanisms;
  `lower_half`, `split_reverse` and `parity_reverse` occur inside that result's proof. Padding
  preserves the parity product even when its two parity classes exchange.
- **Proved:** the order-two case is equality, as shown by the order-two branch of `result`.
  The inequality requires no strictly positive minor or nonsingular-matrix assumption.
- **Source consequence:** the extension of the paper's Theorem 5.1 to all TNN matrices is
  available at every initial split. The paper's negative conclusion for general subsets `I`
  is outside this theorem, whose subsets are specifically `[h]` and its complement.
- **Open:** a general equality characterization, weaker minor hypotheses, and further
  inequalities for non-initial subsets are separate questions, without additional Lean
  conclusions in this module.

## ASSUMED-UNVERIFIED

The prior-resolution screen is bounded to the sources in #13069 and the library note; it is
not an exhaustive worldwide priority determination. The numeric experiments in the probe
are auxiliary evidence and are not the proof. Information-escape registration is paused
under CLAUDE.md §3.9.
