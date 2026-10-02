---
slug: rosenzweig-stanfill-2026-open-problem-1-6-even-residues
bibkey: rosenzweigstanfill2026loglaplacians
doi: 10.48550/arXiv.2606.04225
url: https://arxiv.org/abs/2606.04225v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.result
---

# Rosenzweig–Stanfill even residue vanishing

## Problem

Bart Rosenzweig and Jonathan Stanfill, *On the fundamental solutions of two
nonlocal parabolic equations related to logarithmic Laplacians*,
arXiv:2606.04225v1, Open Problem 1.6(iv), printed page 4:

> Consider the notation of Theorem 1.5. Then the following are conjectured to be true:
>
> (iv) For every α ∈ (0, π), (1.13) is equal to zero whenever m ≥ 0 is even.

The Lean proposition is
`∀ m : ℕ, Even m → ∀ α : ℝ, 0 < α → α < Real.pi → paperBracket m α = 0`.
It includes m = 0 and α = π/2. The bracket uses the literal finite sums
in (1.13), the primary recursive c-array in (1.14), its separate Bernoulli
formula at π/2, and the partial ordinary Bell profile sum in (1.20)–(1.21).
The convention is B₁ = −1/2. Natural subtraction and integer division
are used only in indices; coefficient arithmetic takes place in ℂ.
The external factor 2 exp(γ_E m)/π is nonzero, so the zero bracket gives
the zero value of (1.13).

## Motivation

The even-index cancellation is part of the paper's proposed description
of the zero and nonzero residues of K₂(t,x,x). The preregistered question
is issue #11546; the admission basis is open-problem-resolution.
The mathematical target is the full universal clause (iv), not a finite
collection of even indices or angles.

## Gap

The arXiv version history contains only v1, and its HTML states clause
(iv) as conjectured. OpenAlex work W7163512061 reports zero citations.
Google Scholar reports two citing works: R. A. Chandru, *Arithmetic
identification from interval Weil spectra*, and *Finite noisy determination
of cuspidal representations from interval Weil spectra*. Their complete
Google-cached HTML texts cite the source's heat-kernel continuation;
neither treats this Bell/Bernoulli residue identity. Both texts contain
zero occurrences of “Bernoulli” and “Bell polynomial”. These external
readings were collected at 2026-10-02 09:49–09:52 UTC.
Semantic Scholar returned HTTP 429, so that index supplies no current
reading. Historical openness beyond the checked sources is unverified;
no exhaustive search or priority claim is asserted.

## Route

Let C(s) be the ordinary series of the primary c-array. The module derives
its square inverse-denominator identity from the Euler-derivative
polylogarithm recursion, using an arbitrary-order Stirling coefficient
identity obtained by normalizing the frozen Stirling inclusion–exclusion theorem.
At α = π/2, the separate Bernoulli formula gives a logistic
series and the same square identity. Thus exp(−s/2)C(s) is even.

The b-convolution gives A(s) = C(s)E(s), with E even, so
H(s) = exp(−s/2)A(s) is even and H′ is odd. The residue bracket is the
negative of the Bernoulli residue functional applied to exp(s/2)H′(s).
Bernoulli-polynomial translation at 1/2 identifies the functional on each
monomial. Reflection Bₙ(1−t) = (−1)ⁿBₙ(t) kills odd coefficients at 1/2;
for every even m the functional therefore annihilates H′. All coefficient
sums are finite. Formal power-series substitution requires zero constant
coefficient, not analytic convergence.

The public result has proof_shape content. Its live intermediate content
includes linear_ODE_unique, F_translation,
primary_square_inverse and bernoulli_annihilates. Existing Bernoulli and
geometric-series definitions are used directly. Information-escape
registration is paused under CLAUDE.md §3.9.

## Falsifier

An even natural m and a real α strictly between 0 and π with a nonzero
paperBracket would refute the statement. Finitely many zero values cannot
establish it. The theorem imposes no restriction excluding π/2 and no
positive lower bound on m beyond natural-number membership.

## Evidence

The kernel-checked theorem is
`D5.S3.ArithSums.LogLaplacianEvenResidueVanishing.result`.
The statement uses the original recursion and Bell polynomials, rather
than an assumed generating-function characterization of the c-array.
The axiom closure is propext, Classical.choice and Quot.sound.

## Triage

Resolution: proved for Open Problem 1.6(iv). The utility classification
is none: the module proves an unbounded symbolic identity and contains
no finite enumeration, certificate checker, numerical reduction or
certified numerical instance.

### What the settlement shows

- **Proved in this module:** the decisive mechanism is the combination of
  reflection-evenness after multiplication by exp(−s/2) and Bernoulli
  translation at 1/2. The cancellation covers every even m, including
  zero, and the entire open interval of angles, including π/2.
- **Proved in this module:** the convolution argument preserves the
  reflection-evenness for arbitrary complex d-arrays and weights. The
  specific finite-difference coefficients are needed to identify the
  paper's expression; their detailed values do not drive the parity
  cancellation.
- **Open:** clauses 1.6(i)–(iii), nonvanishing at odd indices, endpoint
  angles, and analytic convergence are outside this settlement. The
  proof gives no nonvanishing or sharpness statement for odd m.
- **Proved in this module:** clause (iv) supplies the even-index vanishing
  statement for the source's residue formula. Conclusions that use this
  cancellation can invoke the proved clause. **Open:** a complete pole
  classification still needs the source's remaining nonvanishing assertions;
  no additional analytic theorem is claimed here.

## ASSUMED-UNVERIFIED

Exhaustive historical openness and priority beyond the searched sources
are unverified. Semantic Scholar was unavailable. The Google-cached
citing texts were read; their original ResearchGate downloads returned
HTTP 403. No claim about model-family independence follows from the
carrier labels.
