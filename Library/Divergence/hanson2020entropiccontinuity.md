---
bibkey: hanson2020entropiccontinuity
authors: Eric P. Hanson
year: 2020
title: "Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels"
doi: null
url: https://arxiv.org/abs/2010.02408v1
claim: "Total-variation balls in the probability simplex admit majorization-minimizers and -maximizers (Chapter 3, Eq. (3.1)), p-norm balls with 1 < p < ∞ do not (Section 3.7), and Chapter 8, Question 1 asks whether balls in the Hellinger distance, the Bures distance, the square-root Jensen–Shannon divergence, Wasserstein distances or other metrics admit majorization-minimizers."
strata_touched:
  - D5/S3/Divergence/JensenShannonBallMajorizationRefutation
license: citation-only
triage: anchor
---

# Hanson, entropic continuity bounds and majorization over balls

E. P. Hanson, *Entropic Continuity Bounds & Eventually Entanglement-Breaking Channels*, PhD thesis, University of Cambridge (2020); arXiv:2010.02408 [quant-ph] (v1 6 October 2020, the only version).

## Verified locator

Source: https://arxiv.org/abs/2010.02408v1; the text was read from the PDF.
- printed page 9 (PDF page 25): majorization, Eq. (2.3);
- printed page 11 (PDF page 27): the total-variation ball and the majorization-minimizer and -maximizer, Eq. (3.1);
- printed pages 41–47 (PDF pages 57–63): Section 3.7, p-norm balls;
- printed page 171 (PDF page 187): Chapter 8, Question 1.

## Source statements

Eq. (2.3): "For x, y ∈ R^d, we say x majorizes y, written x ≻ y, if Σ_{j=1}^k x↓_j ≥ Σ_{j=1}^k y↓_j ∀k = 1, . . . , d − 1, and Σ_{j=1}^d x↓_j = Σ_{j=1}^d y↓_j."

Eq. (3.1): "let r ∈ P be a probability vector, and consider the total-variation ball B_ε(r) := {q ∈ P : TV(r, q) := ½‖r − q‖₁ ≤ ε} for ε > 0. There exists r∗_ε, r∗,ε ∈ B_ε(r) such that r∗_ε ≺ q ≺ r∗,ε ∀q ∈ B_ε(r). We call r∗_ε the majorization-minimizer over B_ε(r), and r∗,ε the majorization-maximizer over B_ε(r)."

Chapter 8, Question 1: "Section 3.7 shows that balls in p-norm with 1 < p < ∞ do not admit majorization-minimizers, while Chapter 3 is dedicated to proving that balls in 1-norm do admit majorization-minimizers (and majorization-maximizers). Do balls in Hellinger distance, Bures distance, the (square-root) Shannon-Jensen divergence, Wasserstein distances, or other metrics on P admit majorization-minimizers?"

The thesis writes log for the base-2 logarithm and ln for the natural logarithm (page 9).

## Reading used by the repository

The repository answers the Jensen–Shannon clause. With J(p, q) = (1/2) Σᵢ [pᵢ ln(2pᵢ/(pᵢ + qᵢ)) + qᵢ ln(2qᵢ/(pᵢ + qᵢ))], the square-root metric is √(J/ln 2), and its closed ball of radius ε around p is the sublevel set {q : J(p, q) ≤ ε² ln 2}. The choice of logarithm base only rescales the radius. The question is read as: for every p and every positive radius, the ball has a majorization-minimizer in the sense of Eq. (3.1).
