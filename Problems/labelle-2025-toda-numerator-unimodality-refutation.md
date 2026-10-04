---
slug: labelle-2025-toda-numerator-unimodality-refutation
bibkey: labelle2025toda
doi: 10.48550/arXiv.2502.10655
url: https://arxiv.org/abs/2502.10655v3
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result
---

# Labelle's Toda numerator unimodality conjecture

## Problem

A. Labelle, "On a specialization of Toda eigenfunctions", arXiv:2502.10655v3,
Section 7, Conjecture 7.3:

> The polynomial $(q)_\alpha^2\mathfrak{J}_\alpha$ is unimodal.

Section 1 fixes a split semisimple Lie algebra over the rationals, its simple
roots, and its invariant form normalized so short roots have squared length 2.
Definition 1.1 defines $\mathfrak{J}_\alpha$ in $\mathbb{Q}(q)$ for every
nonnegative root-lattice coordinate vector. Unimodality means weak increase
up to a peak and weak decrease thereafter.

## Motivation

The paper proves polynomiality and positive coefficients in type A and proposes
unimodality in its general setting. Type C2 belongs to that setting and supplies
a counterexample at $\alpha=2\alpha_1+2\alpha_2$, with the first root short.

## Gap

This is a tier-1 published named conjecture, preregistered in issue #11627.
That issue records the literal source, quantified target, witness, and scoped
literature check. The paper's v3 retains Conjecture 7.3. The reported checks of
arXiv:2510.21319 and arXiv:2509.02881 concern type A, not all-type unimodality;
searches for Labelle/Toda, Zastava/unimodal, and Whittaker/Shapovalov found no
settlement in the searched scope. These literature-search results are
orchestrator-reported; they establish no exhaustive publication priority.

## Route

`CartanDatum r` encodes finite-type symmetrizable generalized Cartan matrices
at every finite rank r: integer matrices on `Fin r`, a symmetric positive-definite
Gram form, positive integer d, G(i,j)=d(i)C(i,j), and G(i,i)=2d(i).
At positive rank, some d(i)=1 normalizes the shortest simple roots to squared
length 2; at rank zero that condition is vacuous. The integral Gram form is
even on all integral coordinate vectors. `claim` quantifies over every rank,
every such datum, and every nonnegative coordinate vector `Fin r → ℕ`.
The module constructs the C2 inhabitant and proves every field obligation:
Cartan [[2,-2],[-1,2]], Gram [[2,-2],[-2,4]], d=(1,2).
The quadratic form is $2(x-y)^2+2y^2$, positive away from zero.

`J` implements Definition 1.1's equation (2), with the self-term moved to the
left, in `RatFunc ℚ`; q remains an indeterminate. `qFactor` is the displayed
product over all coordinates. `quad` chooses the integer half k certified by
$\sum_{i,j}\beta_i G_{ij}\beta_j=k+k$ and uses integer powers, so the
exponent is literally $(\beta,\beta)/2$ with no truncation or conversion to
natural numbers. Recursion descends by total coordinate height; no certificate
values enter these definitions.

Within `result`, all nine values for 0≤a,b≤2 are derived from the recursion by
clearing nonzero denominators. At (2,2), the numerator is

$$
1+q+3q^2+2q^3+5q^4+2q^5+3q^6+q^7+q^8.
$$

Injectivity of the polynomial algebra map identifies any polynomial in `claim`
with this numerator. Degrees 2,3,4 have coefficients 3,2,5: a peak at or before
2 contradicts weak decrease at 3, and a later peak contradicts weak increase
at 2. Unimodality is defined for the finite list of coefficients from degree zero
through `natDegree`, with a peak in that range. No comparison with the
zero tail beyond the degree is imposed, including for signed polynomials.

## Falsifier

The route requires the C2 datum to satisfy all domain constraints, the nine
rational-function identities to follow from the live recursion, all cleared
denominators to be nonzero, and the polynomial algebra map to be injective.
The proof checks these obligations and the two exhaustive peak cases.
A failure of any obligation would invalidate this refutation.

## Evidence

`D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result`
has type `¬ claim`, with no hypotheses. The explicit public surface is
CartanDatum, qFactor, quad, J, Unimodal, claim, c2, and result; height is private.
There are no private theorem declarations or companion results.
The import is `Mathlib.FieldTheory.RatFunc.AsPolynomial`.
The result's axiom closure is propext, Classical.choice, and Quot.sound.

## Triage

`theorem`: Refuted, with admission basis `open-problem-resolution` (#11627).
The judgement form of result is bind-only; escape witness: none. The settlement
is admitted as an external named open-problem resolution. No digestion atom
or coverage claim is attached. Information-escape registration is paused
under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** the actual Definition 1.1 recursion in normalized
  finite type C2 produces the displayed numerator. Its interior strict valley
  rules out every peak, refuting the all-types Conjecture 7.3.
- **Computed:** the coefficient list [1,1,3,2,5,2,3,1,1] is nonnegative and
  palindromic. Those two properties do not imply unimodality; the failure is
  an interior valley rather than a negative coefficient or a zero-tail issue.
  Exact SymPy evaluation of Definition 1.1 also checks these coefficients.
- **Computed:** the same exact recursion gives nonnegative polynomial numerators for
  C2 at all 0≤a,b≤3. The non-unimodal pairs in this window are (2,2), (2,3),
  and (3,3). All A2 pairs with 0≤a,b≤2 are unimodal. These are finite exact
  computations, not unbounded theorems.
- **Open:** positivity Conjecture 7.2 in general, and unimodality restricted to
  type A. The C2 witness satisfies positivity, so the refutation does not
  settle Conjecture 7.2. The paper's proved type-A numerator formula remains
  a literature result, not a new theorem in this module.
- **Open:** a classification of C2 coordinates with unimodal numerators and
  corrected sufficient geometric or root-theoretic hypotheses.
- **Open as a separately formalized consequence:** the proposed general
  smooth-projective-variety explanation via Hard Lefschetz cannot identify
  this C2 numerator with a polynomial forced to be unimodal. Its required
  geometric bridge is not proved here. The source's Conjecture 6.1 is in
  type A; its implication toward type-A unimodality is unaffected. The
  established theorems and Conjecture 7.1's positivity implication do not
  require Conjecture 7.3, so this refutation supplies no refutation of them.

## ASSUMED-UNVERIFIED

The literature check is scoped; citation-index coverage and exhaustive
publication priority are unverified. The root-system interpretation of the Cartan-domain encoding is an expository
identification rather than a separate Mathlib RootPairing equivalence theorem.
