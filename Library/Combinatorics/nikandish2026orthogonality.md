---
bibkey: nikandish2026orthogonality
authors: R. Nikandish
year: 2026
title: "Annihilating-Ideal Graphs and Orthogonality Graphs over F_2"
doi: 10.48550/arXiv.2609.22769
url: https://arxiv.org/abs/2609.22769v1
claim: "Section 4, Problem 4.2 asks for the exact clique number of the orthogonality graph on all nonzero subspaces of F_2^n for general n."
strata_touched:
  - D5/S3/Combinatorics/Orthogonality/NikandishClique
license: citation-only
triage: anchor
---

# Nikandish's subspace orthogonality graph

## Verified locator

DOI: 10.48550/arXiv.2609.22769

URL: https://arxiv.org/abs/2609.22769v1

The primary source is arXiv:2609.22769v1, submitted 19 September 2026.
Its abstract and HTML were retrieved on 22 September 2026. The abstract
exposes v1 and a CC BY 4.0 license. This note contains citation, a short
quotation, and a mathematical mapping, rather than a reproduction of the paper.

## Exact problem

Definition 2.3 uses every subspace of `V_n = F_2^n` as a vertex, with
orthogonality for the standard dot form `B_n(u,w) = sum_i u_i w_i`.
The graph `O_n*` deletes the zero subspace. Adjacency in the simple graph
is between distinct subspaces; there is no restriction on their dimensions,
intersections, or the degeneracy of the restricted form. Section 4 asks:

> Problem 4.2. Determine the exact value of omega(O_n*) for general n.

For every `n >= 1`, the formal consumer answers

    omega(O_n*) = max(n, N(floor(n/2)) + n mod 2),

where `N(r)` is the actual number of nonzero subspaces of `F_2^r`.
The Lean definition is `Nat.card (Vertex r)`. It is an independent finite
lattice cardinality, not a renamed graph invariant. No equality with a sum
of Gaussian binomial coefficients is claimed or needed for this statement.

Theorem 2.4 and equation (4) of the source transfer clique numbers to its
annihilating-ideal graph by adding one. That corollary is not a separate
formal declaration here.

## Source correction and attribution

The proof of Lemma 3.2 says that a two-dimensional space over `F_2` has
exactly three nonzero subspaces, comprising two lines and the whole space.
There are three lines and the whole space, hence four nonzero subspaces.
That counting argument does not establish the asserted bound. The formal
consumer does not use it; its general upper bound includes dimension four.

Section 4 already constructs sixteen vertices for `n = 7` by taking all
fifteen nonzero subspaces of an isotropic three-space and adjoining its
perpendicular space. The odd extra-vertex construction in that dimension
belongs to the source. The general construction below extends it to all
odd dimensions, including `n = 1`.

## Mathematical mechanism

For a clique `C`, let `R` be the sum of `rad(U) = U intersect U-perp`
over `U in C`. Every summand annihilates every member, so every `U` is
contained in `R-perp`, `R <= R-perp`, and `U intersect R = rad(U)`.
Write `r = dim R`; nondegeneracy of the ambient dot form gives `2r <= n`.

Restrict the form to `S = R-perp` and descend it along
`J = R.comap S.subtype`. Each projected clique member in `S/J` has a
nondegenerate restriction: a representative annihilating its own member
lies in its radical and therefore in `R`. The images are pairwise
orthogonal. Pairing a finite zero relation with each member proves indexed
independence, even when the original subspaces overlap. The quotient may
be alternating; no anisotropic-vector choice is used. Independent nonzero
images number at most `dim(S/J) = n - 2r`.

Members contained in `R` inject into its nonzero submodule lattice. A finite
basis transports that lattice to the one defining `N(r)`, preserving bottom.
Thus `|C| <= N(r) + n - 2r`. At `r = 0` this is `n`. For `r >= 1`, embed
`F_2^r` as the first-coordinate-zero hyperplane in `F_2^(r+1)`. In addition
to its embedded nonzero subspaces, the first coordinate line and the whole
space are distinct outside subspaces. Therefore `N(r+1) >= N(r)+2`.
Induction moves the positive-r bound to `r = floor(n/2)`.

The coordinate lines give the first lower bound. For the second, duplicate
the first `t = floor(n/2)` coordinates and set the remaining coordinates
to zero. The image has dimension `t` and is totally isotropic. All its
nonzero subspaces give `N(t)` vertices. In odd dimension its perpendicular
space has dimension `t+1`, so it is a distinct extra vertex adjacent to all
of them. These constructions attain the two endpoints.

## Library reuse and bounded prior evidence

The exact statement was preregistered in repository issue 9458 before
probes. Repository searches at `dbe516012b2554571304c1c312c3e4f3a02f1836`
for the author, arXiv identifier, and target definitions found no matching
theorem. The existing `BinaryCharacterCodeDuality.standardCoordinatePairing`
is reused directly. Pinned Mathlib supplies `LinearMap.liftQ₂`,
`LinearMap.BilinForm.finrank_orthogonal`,
`Submodule.finrank_quotient_add_finrank`,
`Submodule.comapSubtypeEquivOfLe`,
`iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`,
`iSupIndep.subtype_ne_bot_le_finrank`, finite bases, submodule order
isomorphisms, and finite clique cardinality bounds. Their actual source
bodies were inspected; their parameter adaptations remain local to `result`.
The Mathlib revision is `db584cd6d46c92f209a44c0f1c829460d327499d`.

The preceding independent intake inspected related papers on orthogonal
collections of nondegenerate k-planes (arXiv:2004.10742), symplectic frame
complexes (2305.02940), dual polar graphs (1510.01697), polar-point graphs
(2105.03755 and 2402.05055), subspace lattices (2002.00368), and isotropic
quotients (2212.07777). It reported no matching all-subspace theorem.
Its actual third-party Lean body searches in `afflom/emporous`,
`AxiomMath/HJO`, and `AxiomMath/QBinomialTrace` supplied no exact target
or Gaussian subspace-count bridge. Those literature and ecosystem findings
are attributed intake evidence, not an exhaustive search or kernel proof.
The present implementation's attempt to retrieve the cited
`afflom/emporous` file at commit
`58208f5aed07f14de0315e96b6b69f9791153da9` returned HTTP 404 from both
the raw URL and the authenticated GitHub contents API, so that body was
not independently reverified here. No third-party package is imported.

Worldwide absence of an equivalent prior resolution remains
`ASSUMED-UNVERIFIED`. In particular, differently named polar-space results
are not excluded by a bounded negative search. The full formula and radical
family estimate are repository-derived; classical quotient, dimension, and
lattice facts are reused background rather than separate new results.
