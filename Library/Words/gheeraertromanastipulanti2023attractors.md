---
bibkey: gheeraertromanastipulanti2023attractors
authors: France Gheeraert, Giuseppe Romana, Manon Stipulanti
year: 2023
title: String attractors of some simple-Parry automatic sequences
doi: null
url: https://arxiv.org/abs/2302.13647v2
claim: Conjecture 42 gives the minimum string-attractor size of every original fixed-point prefix under weak cyclic maximality.
strata_touched:
  - D5/S1/Words/Attractors/FiniteWordAttractors
  - D5/S1/Words/Attractors/PeriodicPrefixAttractors
  - D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum
license: citation-only
triage: anchor
---

# String attractors of some simple-Parry automatic sequences

Definition 2 supplies the original substitution, its iterates and their lengths.
The unnumbered definition opening Section 4 supplies unrestricted string
attractors. Paper positions are one-based; each paper position is the Lean
zero-based position plus one, preserving cardinality and occurrence intersection.
The working hypotheses fix k >= 2, nonnegative integer coefficients with positive first and last
entries, and the original substitution on k letters. Conjecture 42 concerns
every positive prefix length when the coefficient word with its last entry
decreased by one is a weak lexicographic maximum of its cyclic rotations.

Proposition 4 supplies the original short and full block recurrences.
Lemma 22 and Theorem 23 describe canonical endpoint-attractor intervals;
Proposition 34 connects cyclic maximality with fractional prefixes. These
published statements supply context, not premises of the Lean proof.

The formal proof uses a direct periodic-digit/interior induction and a scan
through all k original blocks. The chosen cap U(n+1)-1 is a proved periodic
prefix; it is not identified with a source maximal fractional exponent.
The proof retains equal rotations, proper powers, unary primitive roots,
allowed zero coefficients and every original prefix length.

The formalization reuses morphismPower, wordPower and pinned Mathlib list and
finite-set APIs. No priority or worldwide novelty claim is made.

The bibkey and year refer to the initial 2023 arXiv submission. The source
used here is v2, dated 22 March 2024, licensed under CC BY 4.0. This Library
note uses citation-only attribution; no external Lean implementation is copied.

## Verified locator

The canonical source is https://arxiv.org/abs/2302.13647v2. The following
locators refer to that exact v2 and its original notation and working
hypothesis (WH): k >= 2, natural coefficients c(0), ..., c(k-1), with
c(0) >= 1 and c(k-1) >= 1; middle coefficients may be zero.

- **Definition 2** defines the morphism on the original alphabet
  {0, ..., k-1}: a < k-1 maps to c(a) zeros followed by the original
  letter a+1, and k-1 maps to c(k-1) zeros. It defines u_n as the n-th
  iterate of the singleton 0 and U_n as its length, with u_0 = 0 and
  U_0 = 1. Under (WH), the fixed point starts with 0.
- **Proposition 4** gives the short recurrence for 0 <= n < k,
  u_n = u_(n-1)^c(0) ... u_0^c(n-1) followed by the original letter n,
  and the full recurrence for n >= k,
  u_n = u_(n-1)^c(0) ... u_(n-k)^c(k-1). These are concatenations of
  literal original blocks; a zero coefficient contributes an empty block.
- The **unnumbered string-attractor definition opening Section 4** ranges
  over all subsets of {1, ..., m}: every nonempty factor must have an
  equal occurrence wholly inside the same finite word and crossing a
  selected position. A paper position p corresponds to Lean position p-1,
  and Lean position q corresponds to paper position q+1. This bijection
  preserves cardinality and occurrence intersection without coding letters.
- **Lemma 22** states P_n <= U_(n+1)-1 under (WH). **Theorem 23** gives
  the endpoint attractor Gamma_(n-1) union {U_n} for m in [U_n, Q_n]
  and Gamma_n for m in [P_n, Q_n], under its fractional-power hypothesis.
  The paper's Gamma_n uses the last at most k iterate endpoints, with
  their one-based positions mapped as above. Here Q_n is the length of
  the longest prefix of the fixed point that is a fractional power of
  u_n. The implementation's cap U_(n+1)-1 is a proved periodic prefix;
  it is not asserted to equal Q_n. The endpoint intervals alone do not
  supply every residual prefix or the full minimum conclusion.
- **Proposition 34**, under (WH), equates its assertion (3), maximality
  of d = c(0) ... c(k-2) (c(k-1)-1) among cyclic rotations, with its
  assertion (1), that every prefix of length U_(n+1)-1 is a fractional
  power of u_n for all n >= 0. Maximality is weak lexicographic
  comparison: every rotation is <= d, including ties. Proper powers
  and unary primitive roots remain allowed, with the original k-letter
  alphabet and substitution retained.
- **Conjecture 42** assumes (WH) and one of the equivalent assertions
  of Proposition 34. For every m > 0, it predicts the unrestricted
  attained minimum i+1 when U_i <= m < U_(i+1), 0 <= i <= k-2,
  and k when m >= U_(k-1). Its s_u(m) corresponds to gamma of the
  original length-m fixed-point prefix, minimizing over all position
  subsets satisfying the Section 4 definition, not only endpoint sets.

These source definitions, published results and the conjecture are provenance
and attribution. They introduce no Lean axiom and are not assumed paper-level
premises of the proof.
