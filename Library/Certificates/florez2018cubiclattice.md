---
bibkey: florez2018cubiclattice
authors: Rigoberto Flórez, Leandro Junes, José L. Ramírez
year: 2018
title: "Further Results on Paths in an n-Dimensional Cubic Lattice"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf
claim: Section 6 states Conjectures 1 and 2 for xz-plane and yz-plane paths in the printed C_3^+(k) family.
strata_touched:
  - D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation
license: citation-only
triage: anchor
---

# Cubic-lattice paths in coordinate planes

Section 1, printed pages 2--3, defines the path families:

> We use C_n^±(k) to mean the set of all paths of length k in the
> n-dimensional cubic lattice. We divide C_n^±(k) into subfamilies depending
> on the behavior of the path. We now give definitions and notation for those
> families. If P = (±e_{j_1})(±e_{j_2}) · · · (±e_{j_k}), then we define
> V_r := (±e_{j_1}) + (±e_{j_2}) + · · · + (±e_{j_r}), the algebraic
> combination of the first r components of P for 0 < r ≤ k, i.e., V_r is the
> sum of the components of any initial subpath of P with r steps. We denote
> C_n(k) the subset of C_n^±(k) formed by all paths
> P = (±e_{j_1})(±e_{j_2}) · · · (±e_{j_k}) that satisfy that the nth
> coordinate of V_k is zero. We use C_n^≥(k) to denote all paths in C_n^±(k)
> with P = (±e_{j_1})(±e_{j_2}) · · · (±e_{j_k}) and that nth coordinate of
> V_r is non-negative for all 0 < r ≤ k. We now let C_n^+(k) be C_n(k) ∩
> C_n^≥(k). [...] For example, Figure 1 depicts the 14 paths in C_2^+(3).
> Figure 2 depicts the 17 paths in C_3^+(2).

The paper defines paths as starting at `p_0 = (0, ..., 0)` with each step in
one of the positive or negative coordinate directions. In the formal reading,
"completely contained in the xz-plane" means that every vertex `V_r` for
`0 < r ≤ k` has second coordinate zero; the yz-plane condition uses the first
coordinate. The initial vertex needs no separate clause because it is the
origin.

Section 6, printed page 23, gives the anchor and the two conjectures:

> **Proposition 20.** For k ≥ 1, the number of paths in C_3^+(k) that are
> completely contained in the xy-plane is 4^k.
>
> **Conjecture 1:** For k ≥ 1, the number of paths in C_3^+(k) that are
> completely contained in the xz-plane is (see Table 4 first line)
> Σ_{i=1}^{k+1} binom(2i,i) binom(k,i−1)/(i+1).
>
> **Conjecture 2:** For k ≥ 1, the number of paths in C_3^+(k) that are
> completely contained in the yz-plane is
> Σ_{i=1}^{k+1} binom(2i,i) binom(k,i−1)/(i+1).

The article says these sequences and conjectures are based on experimentation,
provides no proof or closed formula for them, and leaves them as conjectures for
future work. Table 4 prints `3, 10, 36, 137, 543, 2219, 9285, 39587, 171369`
for each plane and labels the sequence `A002212(k + 1)`.

Under the printed final-zero definition, direct enumeration gives xz-plane and
yz-plane values `2, 5, 14, 42` for `k = 1, 2, 3, 4`. Under the alternate
reading that keeps prefix nonnegativity but omits the final-zero condition, the
values are `3, 10, 35, 126`. These finite readings do not assert a corrected
formula beyond `k ≤ 4` and do not determine the authors' intended reading.

## Verified locator

- URL: https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.pdf
- Scope: Section 1 on printed pages 2--3 and Proposition 20, Conjectures 1--2,
  and Table 4 on printed page 23.
