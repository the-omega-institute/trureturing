---
bibkey: johnsonwakefield2024incidencenearring
authors: John Johnson; Max Wakefield
year: 2024
title: "A non-associative incidence near-ring with a generalized Möbius function"
doi: 10.26493/1855-3974.2894.b07
url: https://arxiv.org/abs/2204.07158v1
claim: "Definition 5.1 defines J by rectangle sums, Definition 6.2 defines its Möbius polynomial, and Question 6.19 asks for a connected nonmodular rank-three matroid with vanishing evaluation at minus one."
strata_touched:
  - D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius
license: citation-only
triage: anchor
---

# Johnson–Wakefield J-Möbius polynomial

## Verified locator

DOI: 10.26493/1855-3974.2894.b07

Source: https://arxiv.org/abs/2204.07158v1

Published in Ars Mathematica Contemporanea 24 (2024), #P2.03.
The page numbers below refer to the published article.

## Source statements

Page 11, Definition 5.1: “Define J : Fl_3(P) → Z for all fixed (x, y, z) ∈ Fl_3(P) by Σ_{(a,b)⊴(x,y,z)} J(a, y, b) = δ_3(x, y, z).”
Here “(a, b) ⊴ (x, y, z) means x ≤ a ≤ y ≤ b ≤ z in P.”

Page 14, Definition 6.2: “Let P be a ranked finite poset and for (x, y, z) ∈ Fl_3(P) let ρ(x, y, z) = 3rk(P) − rk(x) − rk(y) − rk(z). The J-Möbius polynomial of P is M(P, t) = Σ_{(x,y,z)∈Fl_3(P)} J(x, y, z)t^{ρ(x,y,z)}.”

Page 20, Question 6.19: “Is there a rank 3 non-modular connected matroid M such that M(M, −1) = 0?”

The Lean statement quantifies over finite carriers, uses the lattice of flats,
and imposes the defining rectangle equation on partial flags. Its conclusion
is the negative answer. The rank-three evaluation identity is twice the difference between the numbers
of rank-two and rank-one flats. The proof of nonvanishing
does not use connectedness. A rank-zero intersection of two lines may contain
loops. No arbitrary-rank classification is asserted.

## Supplemental computation

The experiment is in the-omega-institute/trureturing-experiments, commit
12e29eb676f5e4845bb9b417bebfd9bfa514bd7a, at docs/reports/johnson-wakefield-2022-rank-three-moebius-question-6-19/check.py.
The script SHA-256 is d564a17d21dca597c2d1d13a9df5892798299334821f5e1da24b8ec674b6f894.
Its recorded exit code is 0 with RESULT PASS: nine rank-three examples and the
source factorizations for U(3,4) and the rank-four M*(K3,3) example.
These computations supplement the Lean proof. The rank-four example is not
formalized here. Literature completeness remains ASSUMED-UNVERIFIED.
