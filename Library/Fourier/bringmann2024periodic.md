---
bibkey: bringmann2024periodic
authors: "Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane"
year: 2024
title: "Periodic sign changes for weakly holomorphic eta-quotients"
doi: 10.48550/arXiv.2409.07164
url: https://arxiv.org/abs/2409.07164v1
claim: "Appendix A Table 1 asks for period-nine signs of normalized Euler quotients, including exponents 9 at 1 and -6 or -10 at 3."
strata_touched:
  - D5/S3/Arith/ModularForms/CubicThetaLattice
  - D5/S3/Arith/ModularForms/CubicThetaCoreProduct
  - D5/S3/Arith/ModularForms/CubicThetaIdentities
  - D5/S3/Arith/ModularForms/EtaSignK6
  - D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation
  - D5/S3/Combinatorics/Partitions/EulerNineComparison
  - D5/S3/Combinatorics/PowerSeries/LaurentSpecialization
  - D5/S3/Arith/ModularForms/WeightedJacobiSpecialization
  - D5/S3/Arith/ModularForms/EulerPentagonalTrisection
  - D5/S3/Arith/ModularForms/EulerNineDissection
  - D5/S3/Arith/ModularForms/EulerNineSquareDissection
  - D5/S3/Arith/ModularForms/EtaSignK10
license: citation-only
triage: anchor
---

# The exact k6 normalized Euler sign question

## Verified locator

DOI: 10.48550/arXiv.2409.07164

URL: https://arxiv.org/abs/2409.07164v1

The inspected v1 primary TeX is `single-source.tex`, extracted text SHA256
`cf5c92e1e04a9310d3ef71f6bd839274bd2c611240fb26d4ae988098a42717ab`.
The introduction defines the coefficients by normalized Euler products.
Appendix A Table 1, HTML locator `A1.T1.4`, contains the exact entry
`1^9 3^(-6)` with the pattern `+-+--++-+`, starting at residue zero.
The author-hosted manuscript dated May 21, 2025, printed p. 21, repeats
this entry; its PDF SHA256 is
`8e07e6cb135e2bbb3c9caa082ed0262c2aa9b6b1bfccd6f0162cc570191ebace`.
The publisher's typeset table was not inspected.

## Exact scope and formal anchors

Write `E(X)=prod_(j>=1)(1-X^j)`. The question concerns every natural
index of `F6=E(X)^9/E(X^3)^6`, including zero. The coefficient is positive
exactly at residues `0,2,5,6,8` modulo nine and negative exactly at
`1,3,4,7`; there are no zero or exceptional entries in the stated claim.
The eta shift is `-3/8` and the weight is `3/2`. These shifts do not rotate
the residue labels of the normalized Euler coefficients.

The formal anchor
`D5/S3/Arith/ModularForms/CubicThetaLattice.norm_theta_dissection`
is a classical lattice intermediate motivated by this question. It is
not the original sign theorem. The later anchor
`D5/S3/Arith/ModularForms/CubicThetaCoreProduct.coeff_core_product`
identifies the full core lattice coefficients with the actual Euler
quotient `E(X^3)^3/E(X)` for every natural index.

`D5/S3/Arith/ModularForms/CubicThetaIdentities.B_dissection` and
`D5/S3/Arith/ModularForms/CubicThetaIdentities.cubic_identity` prove the
two remaining classical Borwein identities from actual products and
complete lattice sums. They are proved in Lean, not premises of the
sign theorem.

`D5/S3/Arith/ModularForms/EtaSignK6.F6` is the actual normalized quotient:
the ninth power of Mathlib's pentagonal Euler series times the sixth
power of the unit inverse of its expansion by three. Its `C6` is the
coefficient at the original natural index.
`D5/S3/Arith/ModularForms/EtaSignK6.five_coefficient_formulas` gives the
two progressions modulo three and the three remaining progressions
modulo nine, with factors `-9`, `27`, `1`, `-6`, and `9`.
`D5/S3/Arith/ModularForms/EtaSignK6.all_index_signs` proves both exact
modulo-nine sign biconditionals and nonvanishing for every natural
index. Ordinary partition positivity, including the empty partition,
supplies strictness at every index. No separate analytic eta bridge is
needed for these source-defined normalized Euler coefficients.

The supplied bounded literature review found no inspected theorem stating
the complete k6 entry. This note asserts no worldwide absence, priority,
unique status, independent formal acceptance, CI success, or publication
of the original-problem resolution. The separate k10 entry is treated
by the additional algebraic chain described below.

Citation and question boundary only; no source text or PDF is vendored.

## Restricted-product auxiliaries for the separate denominator-ten row

The separate v1 Appendix A Table 1 entry `1^9 3^(-10)` asks for the
unshifted coefficients of `E(q)^9/E(q^3)^10`, including degree zero.
Its proposed signs are positive at residues `0,2,5,8` and negative at
`1,3,4,6,7` modulo nine, with no zero or exceptional index. This is a
different endpoint from k6, notably at residue six.

The source derivation *An all-index algebraic route to the denominator-ten
eta signs* (3 November 2026, SHA256
`f9c81115730bc353681e172d5b2ad17d199d66bd4602b56a5da7dfe8e185852b`)
motivates new restricted-product auxiliaries. Write `Q_r` for the actual
restricted partition series excluding residues `0,r,9-r` modulo nine,
and put `A=Q_4`, `B=Q_2`, `C=Q_1`. The new
`EulerNineComparison.coefficient_order` proves `C[n] <= B[n] <= A[n]`
for every natural degree by finite mixed-block cancellation and exact
coefficient stabilization. Its `D` is the actual coloured partition
product with one colour at residues three and six and two at four and
five. Its `multiplicity_relation` proves `AD=BC`, and
`coeff_delta_nonnegative` proves that `AC-CD` is coefficientwise
nonnegative. The product `(1-q)AC` is also proved nonnegative, with
constant coefficient one, degree-one coefficient zero, and coefficients
at least one in every degree at least two.

`RestrictedEulerCancellation` uses Mathlib's general restricted-partition
HasProd supplier (Weiyi Wang, Apache 2.0) to prove exact finite cancellation
for arbitrary allowed-part predicates and injective finite weight families.
These helpers are genuinely used in the comparison proof. The new
comparisons and decompositions are repository-derived implementations of
the supplied source; no literature novelty is asserted for their ordinary
mathematics.

## Exact denominator-ten algebraic chain

`LaurentSpecialization` shifts Laurent row `n` by `T^n`, so the support
condition `k >= -n` permits evaluation through ordinary polynomial
coefficients. Its continuous additive map preserves complete sums and
is multiplicative on supported inputs. `WeightedJacobiSpecialization`
uses the existing Jacobi suppliers to identify every integer monomial
with the limit of its actual weighted Euler products. The substitution
has weights `q^9` and `q^r`; no unrestricted Laurent substitution is used.

`EulerPentagonalTrisection.euler_three_sections` proves the full integer
reindexing `k=3m`, `k=1-3m`, `k=3m-1`. The exponent and sign identities
are exact and the fibres exhaust all integers. `EulerNineDissection`
then cancels actual partition geometric factors to identify
`J_r=E Q_r`, and proves
`R=E(q)/E(q^3)=A(q^3)-qB(q^3)-q^2C(q^3)` in all degrees.

`EulerNineSquareDissection.restricted_cubic_relation` derives
`B^2=AC+qCD` by extracting residue two from the actual cubic theta
supplier and cancelling the constant-one unit `A`. Its positive
decomposition `W=(1-q)AC+q(AC-CD)` proves the difficult third squared
section nonnegative, with constant one, coefficient one equal to zero,
and strict higher coefficients. The other sections
`U=A^2+2qBC` and `V=2AB-qC^2` have every coefficient at least one.

`EtaSignK10.F10` is the actual quotient `E(q)^9/E(q^3)^10`, defined
with the unit inverse of `E(q^3)`; `C10(n)` is its unshifted coefficient.
The exact first cubic lift retains factors `-9` and `27`. Its zero
component is `G10=E(q)^2/E(q^3)^3`, whose sections are `UP,-VP,-WP`.
Every ordinary partition coefficient is at least one, so smoothing
removes the sole auxiliary hole, including the original residue six.
`EtaSignK10.all_index_signs` states both complete sign biconditionals
and nonvanishing for every natural `n`, with positive residues `0,2,5,8`
and negative residues `1,3,4,6,7` modulo nine.
`EtaSignK10.C10_zero` gives the constant one.

These are source-level mathematical anchors, not independent formal
acceptance, official original-problem delivery, literature priority,
unique status, required CI, or merge certification. The classical
Euler/Jacobi and cubic theta mathematics is attributed through the
existing suppliers; the new implementation follows the supplied
algebraic manuscript and does not assert that its identities are new
in the literature.
