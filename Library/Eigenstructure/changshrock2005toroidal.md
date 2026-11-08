---
bibkey: changshrock2005toroidal
authors: Shu-Chiuan Chang and Robert Shrock
year: 2005
title: "Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips"
doi: 10.1016/j.physa.2005.08.076
url: https://arxiv.org/abs/cond-mat/0506274v1
claim: "The paper constructs degree-resolved labelled connectivity transfer matrices for toroidal lattice strips and conjectures the square degree L-1 eigenvalue v^(L-1)(v+q) for all widths and the honeycomb eigenvalue v^(2(L-1))(v+q)^2 for all even widths."
strata_touched:
  - D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb
  - D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare
license: citation-only
triage: anchor
---

# Chang and Shrock: toroidal Potts transfer matrices

The current slice has L cyclically ordered sites. A black circle denotes a specific color assignment. The degree counts distinct assigned colors, and their permutations remain separate connectivity states. In degree L-1 there is either one unmarked singleton and L-1 distinctly marked singletons, or one adjacent marked double block and L-2 marked singletons. The latter adjacency includes the cyclic seam. At width two the two cyclic bonds have the same endpoints; the degree-one basis has three states. At width four the degree-three basis in equation (2.18) has 48 labelled states.

The join of two components carrying different assigned colors is zero. Joining an unmarked singleton to a marked component preserves the latter's label. Detaching the last site carrying a label is zero in this degree block; detaching a site from a marked double block leaves the other site marked and the detached site unmarked. Detaching an unmarked singleton closes that component and contributes q. These are the degree-preserving connectivity join/detach conventions used for equation (2.34).

The longitudinal operator is the ordered product of vI+D at every site. The two transverse operators contain the odd-even and even-odd bonds respectively, with the last bond crossing the seam. Their honeycomb product is (VHtwo)(VHone).

For square strips, the transverse operator instead contains all L cyclic bonds,
including the seam, and the transfer operator is VH. At width two the two
transverse bonds coincide and both factors remain in the product. Equation
(5.18) conjectures the Tutte eigenvalue x at every width. Its Potts form in
(5.21) is v^(L-1)(v+q), with no parity restriction.

## Verified locator

- Source: https://arxiv.org/abs/cond-mat/0506274v1
- DOI: https://doi.org/10.1016/j.physa.2005.08.076 (Physica A 364 (2006), 231–262).
- Section II, pp. 6–16: the degree-resolved color assignments, black circles, retained label permutations, bases (2.16)–(2.18), and honeycomb join/detach products (2.34)–(2.35).
- Section V.C, p. 32, equations (5.20)–(5.21): the width-four eigenvalue and the all-width conjecture. The conjecture sentence is: "We conjecture that all of the toroidal strips of the honeycomb lattice have this eigenvalue."
- Section V.C, p. 32, equations (5.18), (5.21): the square eigenvalue x and its Potts form v^(L-1)(v+q). The conjecture sentence is: "This also appears for degree d = Ly − 1 in the case of the cyclic square-lattice strips, and we conjecture that all the toroidal square-lattice strips have this eigenvalue."
- Section VI.A, p. 33: "The toroidal strip of the square lattice with width Ly = 2 is equivalent to the ladder graph with all the transverse edges doubled."
- Immediately before (2.34): "Notice that for the honeycomb lattice, the number of vertices in the transverse direction, Ly, should be an even number, and the smallest value without degeneracy is Ly = 4."
- After Figures 2–3: "In addition, it is necessary to include all the arrangements of black circles when the transfer matrix is constructed."
