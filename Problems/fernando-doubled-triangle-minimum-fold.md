---
slug: fernando-doubled-triangle-minimum-fold
bibkey: fernando2026goodcolorings
doi: 10.48550/arXiv.2611.12065
url: https://arxiv.org/html/2611.12065v1#Thmquestionx2
triage: theorem
motivation_gids:
  - D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness
---

# Uniqueness at the fold minimum of a doubled triangle

## Problem

Lakshitha Fernando, Eranda Dhananjaya, Rajitha Ranasinghe, and Dinusha
Priyadarshani ask the second concluding question in §6 of *Good colorings
of doubled triangles and a conjecture of Schwartz*, arXiv:2611.12065v1.

> Up to the symmetries of 𝒯(n) and swapping colors, is ℬₙ the only good coloring of 𝒯(n) with fold count 3n?

For each positive integer $n$, the doubled subdivision glues matching
boundary edges and vertices of two triangular sheets of side length $n$.
A coloring is good when the black minus white count of incident face
corners is divisible by three at every vertex. Each edge whose incident
faces have different colors contributes one fold. At $n=1$ the two faces
share three distinct seam edges.

## Motivation

Proposition 3.3 gives the coloring $\mathcal{B}_n$ with a black front and
a white back, and §§4.1–4.3 show that $3n$ is the minimum fold count. The
equality question asks for the full class attaining that minimum.

## Gap

The lower-bound argument counts crossings of three families of rings.
At equality every cut has two folds. Classifying the colorings requires
locating those folds and determining how the resulting unfolded edges
constrain colors on the two sheets.

## Route

Each fold crosses two coordinate cuts. Each cut meets at least two folds,
so equality in the count forces exactly two per cut. At each side, the
two corner seam folds leaving the side exhaust its nearest parallel cut.
The unfolded edges in the fans between successive side faces propagate
the corner color along the side on each sheet. The two sheets have
opposite corner colors, so all seam edges fold. These $3n$ seam edges
exhaust the total. Face adjacency within each sheet is connected, so
each sheet has a uniform color.

## Falsifier

A positive side length and a good coloring with $3n$ folds that varies
within a sheet or uses the same uniform color on both sheets would
refute the forward implication. An opposite-uniform coloring that fails
goodness or has a fold count different from $3n$ would refute the converse.

## Evidence

The frozen Lean theorem is
`D5.S0.FiniteGeometry.DoubledTriangleFolds.minimum_fold_uniqueness`.
For every natural $n>0$ and every binary face coloring $C$, the conjunction
of goodness and `foldCount C = 3 * n` holds if and only if there is a
Boolean $b$ such that $C$ assigns $b$ to every cell of the fixed front
sheet and its Boolean complement to every cell of the fixed back sheet.
The converse gives goodness and exactly the seam folds for either choice
of $b$. The theorem uses `Classical.choice`, `Quot.sound`, and `propext`.

## Triage

The source question has an affirmative answer. The two colorings on the
fixed sheets are $\mathcal{B}_n$ and its global color swap. The identity
triangulation symmetry suffices in both cases. This settles the second
concluding question for every positive side length.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and historical priority are unverified.
