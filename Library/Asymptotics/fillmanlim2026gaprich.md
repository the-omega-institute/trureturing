---
bibkey: fillmanlim2026gaprich
authors: Jake Fillman and Yi-Sheng Lim
year: 2026
title: On the identification of certain classes of gap-rich sets
doi: 10.48550/arXiv.2609.21029
url: https://arxiv.org/abs/2609.21029v1
claim: Definitions 2.2, 2.3, 2.7 and 2.9 fix the word metric and Schrödinger gap-richness; Section 6 Question 2 asks about unions, sums and Cartesian products.
strata_touched:
  - D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup
  - D5/S3/Analytic/Spectral/FillmanLimGapRichWords
  - D5/S3/Analytic/Spectral/FillmanLimGapRichClosures
license: citation-only
triage: anchor
---

# Gap-rich sets and operations

## Verified locator

DOI: 10.48550/arXiv.2609.21029

Source: https://arxiv.org/abs/2609.21029v1

## Question 2

Page 20, Section 6:

“If X₁, X₂ ⊆ ℝᵏ and X₃ ⊆ ℝˡ are gap-rich, are any of the following sets X₁ ∪ X₂, X₁ + X₂, and X₁ × X₃ gap-rich?”

The question quantifies over positive dimensions and imposes no compactness or
perfectness hypothesis. The three assertions are alternatives; refuting their
disjunction answers each negatively.

## Definitions

Page 5, Definition 2.2: “Given a metric space (Y,d) and k ∈ ℕ, we denote a typical
element in the product space Yᵏ by y = y₁⋯yₖ. We refer to y as a word.”
The displayed concatenation is y♯z = y₁⋯yₖz₁⋯zₗ ∈ Yᵏ⁺ˡ.
“The set of words over Y is denoted by” Y⋆ := ⋃ₖ₌₁∞ Yᵏ.
“For y ∈ Yᵏ, z ∈ Yˡ, we define” d(y,z) := sup over 1 ≤ j ≤ kl of
d((y♯ˡ)ⱼ,(z♯ᵏ)ⱼ).
“We denote by y♯ᵐ the result of concatenating m copies of y.”

Page 5, Definition 2.3: “Given a function A : Y × ℝ → SL(2,ℝ), there is a unique
extension A : Y⋆ × ℝ → SL(2,ℝ) such that” A(y♯z,E) = A(z,E)A(y,E).

Page 6, Definition 2.7: “We say that A is gap-rich with exceptional set S ⊆ ℝ if
S is discrete, and, for all E ∈ ℝ∖S, x ∈ Y⋆, and ε > 0, there exist
y = y(E,x,ε) ∈ Y⋆ such that” (i) d(x,y) < ε, and (ii) A(y,E) is hyperbolic.
“When the exact form of S is unimportant, we shall omit any mention of S and
simply say that A is gap-rich. We say that X ⊆ Y is gap-rich for A if the
restriction A|X×ℝ is gap-rich.”

Page 7, Definition 2.9: “The transfer matrix T : ℝ × ℝ → SL(2,ℝ) for the
Schrödinger operator on ℓ²(ℤ), is given by” T(x,E) = [[E−x,−1],[1,0]].
“In accordance with Definition 2.3, we also denote by T the unique extension
of T to ℝ⋆ × ℝ satisfying (2.2).”
“As above, we then simply say that a set X ⊆ ℝᵏ is gap-rich if T|X×ℝ is gap-rich
in the sense of Definition 2.7.”

The formal encoding uses positive word lengths, zero-based finite indices,
Euclidean block coordinates, reversed transfer multiplication and ordered
coordinate concatenation for the Cartesian product. The transfer determinant
is one. The exceptional set may be any discrete set.

## Scope

The repository result uses the separated vertical components directly. Inputs
have empty exceptional set; each of the three outputs fails at a nondiscrete
set of energies. Compact-perfect strengthening, minimum dimensions and
classification in Question 1 remain open here. The source's restricted
sufficient criteria retain their stated hypotheses.

The literature screen is recorded in issue #29166. Completeness of that screen
is ASSUMED-UNVERIFIED; no certified originality claim is made.
