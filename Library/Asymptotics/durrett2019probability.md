---
bibkey: durrett2019probability
authors: Rick Durrett
year: 2019
title: "Probability: Theory and Examples, Fifth Edition"
doi: 10.1017/9781108591034
url: https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf
claim: "Exercise 3.2.9 gives uniform convergence to a continuous distribution function; Theorem 3.2.9 gives bounded-continuous weak tests and Theorem 4.6.3 uses continuous clipping and absolute tails."
strata_touched:
  - D5/S3/Analytic/Probability/UniformCDFConvergence
  - D5/S3/Analytic/Probability/FirstMomentWeakLimit
license: citation-only
triage: anchor
---

# Probability: Theory and Examples

## Verified locator

DOI: 10.1017/9781108591034

Source: https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf

## Cited result

Exercise 3.2.9, printed page 124:

> If $F_n \Rightarrow F$ and $F$ is continuous then $\sup_x |F_n(x)-F(x)| \to 0$.

The delivered uniform-CDF theorem states the monotonicity, boundedness and tail
conditions explicitly. Its proof uses a finite compact cover and the two tails.
The characteristic-function corollary combines this result with Mathlib's
Lévy continuity theorem. The proof of Theorem 2.4.9, printed page 79, also
states the pointwise-to-uniform principle for nondecreasing functions.

## First-moment truncation

Section 4.6, printed pages 244–246, defines uniform integrability using
absolute first-moment tails. The proof of Theorem 4.6.3 on printed page 245
uses the continuous clamp
$\varphi_M(x)=\max(-M,\min(M,x))$ and the inequality
$|x-\varphi_M(x)|\leq |x|\mathbf{1}_{\{|x|>M\}}$.
Theorem 3.2.9 on printed page 119 characterizes weak convergence by bounded
continuous real tests. These are the classical ingredients for the
varying-law truncation argument; Theorem 4.6.3 itself assumes convergence
in probability and is not cited as a verbatim varying-law theorem.

`FirstMomentWeakLimit.tendsto_integral_displacement` applies this method to
Borel probability measures on the real plane. Weak convergence, integrable
coordinates for every law and its limit, and uniform absolute coordinate
tails imply convergence of the integral of $(y-x)h(x)$ for each bounded
continuous real $h$. The bounded continuous approximant is
$(\varphi_M(y)-\varphi_M(x))h(x)$, with the joint law unchanged. Its
sequence error is bounded by the sum of the coordinate tails times the
bound on $h$; dominated convergence controls its limit-law error. The Lean
proof directly uses pinned Mathlib bounded-continuous weak tests, Bochner
integral inequalities and dominated convergence. No source code is copied
from the book, and no originality claim is made.
