---
slug: abdesselam-2022-pgg-non-half-integer-exponent-refutation
bibkey: abdesselam2022nonabelian
doi: 10.48550/arXiv.2207.07603
url: https://arxiv.org/abs/2207.07603v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.result
---

# Abdesselam's Problem 3: the PGG inequalities at arbitrary positive exponents

## Problem

Abdelmalek Abdesselam, “Non-Abelian correlation inequalities and stable
determinantal polynomials”, arXiv:2207.07603v2, Problem 3, printed p. 14:

> In the light of investigations of spin models with non-integer number of
> components N, as in [8], it would be interesting to see if Thm. 2.3 still
> holds for P^{−η} where η is any positive real number instead of being
> restricted to half integers.

The question concerns all of Theorem 2.3 (p. 10). For real symmetric positive
semidefinite q by q matrices A_j with positive definite sum, let
P(x) = det(Σ_j x_j A_j). Given a parity homomorphism ρ from ℤⁿ to (ℤ/2ℤ)ᴸ,
an even multi-index lies in its kernel. For every m ≥ 0, natural m by n matrix
V with even 1_m V, signs ε_i in {−1,1}, and positive even natural padding u,
the proposed extension requires

$$
\sum_{\substack{\alpha,\beta\in\mathbb N^m\\\alpha+\beta=\mathbf 1_m}}
\mathbf 1\{\alpha V\text{ even}\}\,\varepsilon^\beta
P(u+\alpha V)^{-\eta}P(u+\beta V)^{-\eta}\geq 0
\quad\text{for every real }\eta>0.
$$

The Lean `claim` retains these quantifiers and premises, including L = 0.
Row-vector multiplication uses Mathlib `Matrix.vecMul`.
The single public settling theorem `result : ¬ claim` answers this question
negatively. Problem 3's subsequent question about characterizing distributions
with bilinear positivity is a separate open boundary.

## Motivation

Theorem 2.3 proves the PGG inequalities for positive half-integer exponents.
The proposed extension would remove that restriction for determinantal
polynomials. One admissible negative sum suffices to refute the extension.

## Gap

Tier 1, preregistered before Lean in issue #11488. The v2 paper labels this an
open problem. The issue's scoped literature check found no settlement: the
single citing paper arXiv:2506.06894 uses a symmetrization trick and does not
address Problem 3; INSPIRE agrees on that citing work, and the listed MathDB
queries found only unrelated Abdesselam problems. This establishes
`not-found-in-searched-scope`, without a claim of exhaustive priority.

## Route

Use η = 1/4, n = 3, q = 2, L = 0 and the zero parity map. Set
A₀ = [[1,0],[0,0]], A₁ = [[0,0],[0,1]], A₂ = [[1,1],[1,1]].
Their quadratic forms are v₀², v₁² and (v₀+v₁)², and the sum has quadratic
form v₀²+v₁²+(v₀+v₁)², strictly positive on nonzero vectors.
Consequently P(x) = x₀x₁+x₀x₂+x₁x₂.

Take m = 4, padding u = (1,1,1), all signs −1, and rows
(1,0,0), (1,0,0), (0,1,0), (0,0,1). The sixteen summands combine into
Θ = 2·48^(−1/4) − 4·55^(−1/4) + 2·56^(−1/4)
− 4·60^(−1/4) + 4·64^(−1/4).

Integer fourth-power comparisons give
48·3800⁴, 56·3656⁴, 64·3536⁴ > 10¹⁶ and
55·3672⁴, 60·3593⁴ < 10¹⁶. Real-power monotonicity supplies upper
bounds for the positive-coefficient terms and lower bounds for the
negative-coefficient terms. Therefore
Θ < (2·3800 − 4·3672 + 2·3656 − 4·3593 + 4·3536)/10000
= −1/2500 < 0.

## Falsifier

This refutation would fail if a matrix were not positive semidefinite, their
sum were not positive definite, the parity/sign/padding conditions failed,
the binary enumeration differed from α+β=1_m, or the strict real-power bound
had the wrong direction. All these obligations are discharged inside `result`.
The negative sum breaks the proposed conclusion while satisfying the source
hypotheses.

## Evidence

`D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.result`
has the closed Lean type `¬ claim`. Its proof uses the pinned Mathlib matrix
quadratic-form criteria, exact sixteen-term evaluation, `Real.mul_rpow`,
fourth-power monotonicity, and rational arithmetic. Its axiom closure is
`propext`, `Classical.choice`, `Quot.sound`. No floating-point computation,
`native_decide`, `sorry`, or new axiom is used.

## Triage

`theorem`. The fully quantified positive-exponent extension is refuted.
The proof is bind-only under repository normalization rules; the admission
basis is the preregistered external open-problem resolution in #11488.

### What the settlement shows

- [proved: D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.result]
  The witness satisfies every matrix, parity, sign and padding premise, but
  the four-row alternating sum is less than −1/2500 at η = 1/4. Its repeated
  first-coordinate row gives a second difference in that direction, combined
  with first differences in the other two directions. For
  P(x) = x₀x₁+x₀x₂+x₁x₂ the sixteen terms have the signed product weights
  (48,2), (55,−4), (56,2), (60,−4), (64,4). Positive determinant values and
  a positive definite matrix sum therefore do not ensure this higher-order
  positivity, even with trivial parity. The arbitrary-exponent extension
  cannot serve as a universal premise for further conclusions.
- [computed: python3/SymPy, differentiate L=(x₀x₁+x₀x₂+x₁x₂)^(-η), sum
  (−1)^|c|·∏ⱼ binomial(aⱼ,bⱼ)·∂^b L·∂^c L over b+c=a, and substitute
  x=(1,1,1); a=(1,1,0): 2η/(9·3^(2η)), at η=1/4: √3/54;
  a=(2,1,1): 4η(2η−1)/(27·3^(2η)), at η=1/4: −√3/162]
  The source's Hirota bilinear expression has positive second-order and
  negative fourth-order values at the same point and exponent. The computed
  fourth-order formula is negative throughout 0<η<1/2; it identifies the
  higher-order requirement in Lemma 3.1 that an extension must address.
  This derivative calculation is not a proof of a uniform range for the
  discrete, naturally padded PGG inequalities.
- [computed: python3/SymPy, enumerate α∈{0,1}^m with u=(1,1,1), zero parity
  and all signs −1, summing (−1)^(m−|α|)·(P(u+αV)P(u+(1−α)V))^(-1/4);
  V=(e₀,e₁): 0.009174812609928953398548585398933696045770;
  V=(e₀,e₁,e₂): 0]
  These two lower-order instances survive at η=1/4. For the three-row
  computation, complementary binary vectors cancel exactly; these particular
  values do not establish positivity for all choices with fewer rows.
- [computed: python3/SymPy, evaluate 2·48^(-η)−4·55^(-η)+2·56^(-η)
  −4·60^(-η)+4·64^(-η) with N(expression,40);
  η=1/10: −0.001136841339408331034554767126834078551553;
  η=1/3: −0.0004811008659742435106067947269541444740574;
  η=1/2: 0.0001787070423213465846999433439361998621470;
  η=1: 0.0004870129870129870129870129870129870129870;
  η=3/2: 0.0001859143688166818405210279235084573359397]
  The same finite witness gives two further negative numerical controls and
  three positive half-integer controls. The positive controls agree with the
  range of Theorem 2.3, without checking that theorem's universal quantifiers.
- [computed: python3/SymPy, replace each Aⱼ by Aⱼ+I/100, compute eigenvals()
  and enumerate the same sixteen terms with exact rational determinants and
  N(sum,40); individual spectra: (1/100,101/100), (1/100,101/100),
  (1/100,201/100); sum spectrum: (103/100,303/100);
  Θ at η=1/4: −0.0006058571894597661231544350568493725959128]
  The numerical failure persists when every coefficient matrix is positive
  definite. This supplies a candidate against repairing the extension merely
  by excluding singular coefficient matrices; the perturbed counterexample
  is not kernel-checked here.
- [open] Determine the full exponent range for all PGG inequalities of this
  polynomial, and for general stable determinantal polynomials. Whether
  commutation or simultaneous diagonalization restores the arbitrary-exponent
  assertion is a separate question; neither the sampled exponents nor the
  local derivative formula settles these uniform statements.
- [open] The source's Theorems 2.1–2.3 in their stated ranges require separate
  formal verification; the half-integer statement is not the refuted
  arbitrary-exponent extension. Problem 3's characterization of distributions
  satisfying Lemma 3.1 must distinguish second-order positivity from the
  fourth-order obstruction computed above. No characterization, or settlement
  of the neighbouring spin-model Problems 1, 2 and 4, follows from this module.

## ASSUMED-UNVERIFIED

The literature status in #11488 is a scoped search result, not an exhaustive
priority determination. The citing-work and MathDB checks are attributed to
the named producers in that issue; this dossier does not claim to re-run them.
Distinct model families for codex-cli and ChatGPT Pro are not established.
