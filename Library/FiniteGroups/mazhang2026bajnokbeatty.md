---
bibkey: mazhang2026bajnokbeatty
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Bajnok–Beatty Conjectures 4.1 and 1.6 (arXiv:2406.04045v1, Section 4, p. 10; Section 1, p. 3): classification and extremal noncyclic order"
doi: "10.5281/zenodo.23931731"
url: "https://doi.org/10.5281/zenodo.23931731"
claim: "Corollary 8: for even c >= 2 and k, s >= 1, if Z/cZ x Z/(ck)Z has an s-spanning pair then its order is at most 2s^2, equality requires c | s, and for odd s the order is at most 2s^2 - 2."
strata_touched:
  - D5/S3/FiniteGroups/EvenFirstInvariantFactor
license: citation-only
triage: anchor
---
<!-- GID: D5/L/FiniteGroups/mazhang2026bajnokbeatty -->
# Even first invariant factor for spanning pairs

## Verified locator

DOI: 10.5281/zenodo.23931731

Source: https://doi.org/10.5281/zenodo.23931731

The written proof is by **Haobo Ma and Wenlin Zhang**, *Bajnok–Beatty Conjectures 4.1 and 1.6
(arXiv:2406.04045v1, Section 4, p. 10; Section 1, p. 3): classification and extremal noncyclic
order*, public version 2 (published 2026-11-03), exact-version DOI
https://doi.org/10.5281/zenodo.23931731, Corollary 8 ("Even first invariant factor", label
`cor:even-factor` in `note.tex`). The problems and the attaining constructions are
B. Bajnok and W. K. Beatty's; see Library note bajnokbeatty2024cayleydiameteroriginal.

## Statement

> Let $c\ge2$ be even and $k,s\ge1$. If $G=\mathbb Z/c\mathbb Z\times\mathbb Z/(ck)\mathbb Z$
> has an $s$-spanning pair, then $|G|\le2s^2$. Equality requires $c\mid s$. In particular, if
> $s$ is odd then $|G|\le2s^2-2$.

An s-spanning pair a, b means every g is xa + yb with integers |x| + |y| <= s. The proof:
the relation lattice K of the pair lies in cZ^2, hence in 2Z^2; for T(u,v) = (u+v, u-v) and
M = T^{-1}K one has [Z^2 : M] = |G|/2, and the argument of the square lemma (Lemma 2), which
only uses K in 2Z^2, puts a representative of every coset of M in {0,...,s-1}^2, so
|G|/2 <= s^2. At equality the near-square rigidity lemma with defect 0 gives a basis with
AB = 0, which puts (s,s) or (s,-s) in K, hence c | s. For odd s equality is impossible, and
4 | |G| sharpens the bound to 2s^2 - 2. The source notes that this extends the even-c part of
Bajnok and Beatty's Theorems 1.8 and 3.2(1), which assume a spanning pair of the special form
{(1,u),(1,v)}.
