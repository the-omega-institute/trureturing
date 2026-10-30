---
bibkey: petrovscott2026clone
authors: Leonid Petrov and Jeanne Scott
year: 2026
title: Random Fibonacci words via clone Schur functions
doi: 10.1017/fms.2025.10165
url: https://arxiv.org/abs/2412.21126v2
claim: "Conjecture 6.3: There exist values of ρ and q for which the following specialization (which we call the alternative q-Charlier) is Fibonacci positive."
strata_touched:
  - D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1017/fms.2025.10165

Source: https://arxiv.org/abs/2412.21126v2

Forum of Mathematics, Sigma 14 (2026), e15. The locators below refer to
the pagination of arXiv version 2.

## Source statements

> Define two sequences of tridiagonal determinants as follows:

Equation (2.10), p. 15, defines the determinants of the two displayed
tridiagonal matrices. The first has diagonal x₁, x₂, …, superdiagonal
y₁, y₂, … and subdiagonal one. The second has first row y₁, x₁y₂, 0, …,
then diagonal x₃, x₄, …, superdiagonal y₃, y₄, … and subdiagonal one.

> Here ℓ ≥ 0. For a sequence u⃗ = (u₁, u₂, …), denote its shift by u⃗ + ℓ = (u₁₊ℓ, u₂₊ℓ, …), where ℓ ∈ ℤ≥0.

Definition 2.5, p. 15:

> For any Fibonacci word w, define the (biserial) clone Schur function s_w(x⃗ | y⃗) through the following recurrence: s_w(x⃗ | y⃗) := A_k(x⃗ | y⃗), if w = 1^k for some k ≥ 0; B_k(x⃗ + |u| | y⃗ + |u|) · s_u(x⃗ | y⃗), if w = 1^k2u for some k ≥ 0.

Definition 4.1, p. 21:

> If s_w(x⃗ | y⃗) > 0 for all w ∈ 𝕐𝔽, we say that (x⃗, y⃗) is Fibonacci positive.

Conjecture 6.3, p. 31:

> There exist values of ρ and q for which the following specialization (which we call the alternative q-Charlier) is Fibonacci positive:

$$
x_k=\frac{q^{k-1}(1+\rho q^{k-2}+\rho q^{k-1}-\rho q^{2k-2})}
{(1+\rho q^{2k-3})(1+\rho q^{2k-1})},\qquad
 y_k=\frac{\rho q^{3k-2}(1-q^k)(1+\rho q^{k-1})}
{(1+\rho q^{2k})(1+\rho q^{2k-1})^2(1+\rho q^{2k-2})},\qquad k\ge1.
$$

## Mathematical correspondence

Words are lists over {1, 2}; their weight is the sum of their letters.
Sequences are functions from Nat to Real, used from index one. The source's
shift is written as `fun k => u (k + offset)` inside the recursion. The
auxiliary recursion counts leading ones; `s` starts that count at zero.
`xAQC` and `yAQC` retain the displayed rational expressions and integer
exponents. The existential proposition uses these two sequences without
restricting either real parameter; the proof takes both equal to 1/4.

## Literature boundary

The source and the literature screen in
[18756](https://github.com/the-omega-institute/trureturing/issues/18756)
identify Conjecture 6.3 as an open positivity problem. Completeness of
that prior-art screen is ASSUMED-UNVERIFIED. The Lean result establishes
the existential assertion, without an exact positivity region or a scaling limit.
