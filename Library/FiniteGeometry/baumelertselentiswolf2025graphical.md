---
bibkey: baumelertselentiswolf2025graphical
authors: Ämin Baumeler; Eleftherios-Ermis Tselentis; Stefan Wolf
year: 2025
title: Graphical Tests of Causality
doi: 10.1016/j.jlamp.2026.101133
url: https://arxiv.org/abs/2511.22552v1
claim: "After Definition 13, page 24: We know that Q̃_n^src = Q_n^src for n ≤ 4. In general, this identity is unsolved."
strata_touched:
  - D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope
license: citation-only
triage: anchor
---

# Graphical Tests of Causality

## Verified locator

DOI: 10.1016/j.jlamp.2026.101133

Source: https://arxiv.org/abs/2511.22552v1

Journal of Logical and Algebraic Methods in Programming 151 (2026), 101133.
The locators below refer to the arXiv v1 pagination.

## Source statements

Section 2, page 6: “For a digraph D with V(D) = [n], we use
α(D) ∈ {0, 1}^{n(n−1)} for the adjacency vector with
α(D)_{i,j} = 1 ⇔ i j ∈ A(D).”

Theorem 3, page 17: “The set of digraphs Γ(P_n^causal) is the set of
all digraphs on n vertices with at least one source vertex:”
Γ(P_n^causal) = {D | V(D) = [n], ∃i ∈ [n] : deg_D^in(i) = 0}.

Definition 8, page 17: “The polytope of source digraphs is
Q_n^src := conv(Γ(P_n^causal)).”

Definition 9, page 17: “For any function f : [n] → [n] without
fixed-points, i.e, with ∀i : f(i) ≠ i, the kefalopoda κ_f is”
V(κ_f) = [n], A(κ_f) = {f(i) i | i ∈ [n]}.

Definition 13, page 24: “The polytope Q̃_n^src ⊆ ℝ^{n(n−1)} is the
set of vectors that satisfy the following inequalities:” (58)–(60).
The three families are (−1_{i,j}, 0), (1_{i,j}, 1) for n ≥ 3,
and (α(κ_f), n − 1) for every fixed-point-free f; an inequality
(w, c) means w · x ≤ c.

After Definition 13, page 24: “We know that Q̃_n^src = Q_n^src for
n ≤ 4. In general, this identity is unsolved.”

## Mathematical scope

The Lean statement ranges over every natural n ≥ 2. Vertices are `Fin n`;
arcs are ordered pairs `(s, r)` with `s ≠ r`; an arc set is a finite set
of such pairs. The adjacency function is one on the arc set and zero
elsewhere. A source is a vertex receiving no arc. The real convex hull
of these vectors is compared with precisely the three inequality families.
The coordinate upper bound is assumed only for n ≥ 3, as in (59).

The proof uses incoming-column maxima and a convex mixture of fixed-source
unit boxes. It does not formalize facet dimension or the lifted correlation
polytope of Definition 14. Literature-search completeness and the independent
full journal-text comparison are ASSUMED-UNVERIFIED.
