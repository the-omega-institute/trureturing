---
bibkey: odonnell2014boolean
authors: Ryan O'Donnell
year: 2014
title: Analysis of Boolean Functions
doi: null
url: https://www.cs.cmu.edu/~odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf
claim: A function on the independent sign cube has a unique multilinear expansion; normalized parity characters give coefficient recovery and Parseval's identity.
strata_touched: []
license: citation-only
triage: anchor
---

# Analysis of Boolean Functions

The author-hosted PDF, chapter 1, Theorem 1.1 (printed p.22),
Theorem 1.5 (§1.3), Proposition 1.8 and Parseval's Theorem
(printed p.25), supplies the real sign-cube identities

$$
F(s)=\sum_{b\in\{0,1\}^d}c_b\prod_j s_j^{b_j},\qquad
c_b=2^{-d}\sum_{s\in\{-1,1\}^d}F(s)\prod_j s_j^{b_j},
$$

$$
2^{-d}\sum_s F(s)^2=\sum_b c_b^2.
$$

The normalization is uniform on all $2^d$ independent signs.
The character orthogonality proof also gives the complex version with
absolute squares, by applying the real identity to real and imaginary
parts. The coordinate substitution $s_j=1-2t_j$ connects this unique
multilinear polynomial to corner interpolation on $[0,1]^d$.

These ingredients are consumed in the guarded five-mode response bridge
in §§1–2 of [the seams continuation](../../docs/develop/theory/AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md).
A diagonal restriction $s_1=\cdots=s_d$ does not retain independent
characters. Sign evaluations of a response polynomial are formal probes;
the book supplies no quantum instrument, physical phase realization or
probability law for the FIB source.
