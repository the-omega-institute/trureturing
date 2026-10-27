---
slug: saaltink-2025-q-transversal-representability
bibkey: saaltink2025qtransversals
doi: 10.48550/arXiv.2503.12201
url: https://arxiv.org/abs/2503.12201v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/QTransversalRepresentability.result
---

# Every q-transversal matroid is representable over a finite extension

## Problem

M. Saaltink, *A theory of q-transversals*, arXiv:2503.12201v1, Section 4.2, page 14, states:

> Conjecture 3. All q-transversal matroids are representable.

The [source note](../Library/FiniteGeometry/saaltink2025qtransversals.md) records Definition 14, Theorem 15 and the representation convention of Section 3.2. The preregistration is [#19965](https://github.com/the-omega-institute/trureturing/issues/19965). The settling declaration is `D5/S3/Combinatorics/Matroids/QTransversalRepresentability.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite field $\mathbb F_q$ | `F`, `Field F`, `Fintype F` | Arbitrary finite field |
| Finite family of subspaces of a finite-dimensional vector space | `m`, `k`, `X : Fin k → Submodule F (Fin m → F)` | Coordinates identify the ambient space with $F^m$ |
| Every basis of a partial q-transversal admits a partial avoiding transversal | `IsPartialQTransversal` | Every independent finite spanning set admits an injective assignment to indices, with each vector outside its assigned subspace |
| Rank of the q-transversal matroid | `qTransversalRank` | Supremum of dimensions of partial q-transversals contained in the argument subspace |
| Section 3.2 matrix rank | `representedRank` | Rank of the representing matrix times the transpose of a basis-coordinate matrix |
| One representing matrix for the whole q-matroid | `claim`, `result` | One extension and one matrix give equality of the two ranks for every subspace |
| A field extending $F$ | `Algebra F K`, `FiniteDimensional F K` | A finite-dimensional extension strengthens the source requirement |

The source's phrase “a dimension n subspace” in the partial definition is read with Theorems 15 and 18, which treat partial q-transversals in every dimension. The public definitions and claim retain the literal conventions of #19965. No assumption that the family is coordinate or nested is imposed.

## Motivation

The source proves the coordinate-family case in Theorem 24. The arbitrary-family representation gives a simultaneous matrix realization even when the subspaces have no common coordinate presentation.

## Gap

The literature screen recorded in #19965 covers the source and A. Fulcher, *A cyclic flat embedding theorem for transversal q-matroids*, arXiv:2603.13550v1, together with the recorded arXiv and repository searches. That screen found no unrestricted representation theorem. Its completeness and publication priority are `ASSUMED-UNVERIFIED`.

## Route

For each family member $X_i$, use its annihilator in the dual space. The private `hall_criterion` relates the every-basis avoidance condition to dimension inequalities. The private `restricted_annihilator_hall` supplies the deficit Hall inequalities for the restricted annihilators. `D5.S3.Combinatorics.Matroids.LinearRado.spanning_representatives` then supplies a spanning selection, and `D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows` extracts a nonzero minor. The private `generic_minor_nonzero` establishes such a minor for each partial q-transversal.

There are finitely many subspaces over the finite base field. The private `simultaneous_specialization` preserves the finite family of selected nonzero minor polynomials in one finite extension. The private `specialized_independent_subspaces` therefore gives one linear map, vanishing on each assigned $X_i$ coordinate, whose images are independent on every partial q-transversal.

Conversely, `D5.S3.Combinatorics.Matroids.LinearRado.independent_support_matching` turns independent image vectors into an avoiding assignment. The private `imageRank_attained` finds a subspace attaining the image rank, and `qRank_eq_imageRank` identifies the two rank functions. The private `representedRank_matrixOfLinear` expresses the image rank as the required matrix rank. `result` combines these statements.

## Falsifier

A finite field and a finite subspace family whose rank function cannot be represented over any finite extension would contradict `result`. Testing a single proposed matrix is insufficient: the assertion permits a choice of extension and matrix. Numerical agreement on sampled families supplies finite evidence only.

## Evidence

The Lean sources are [LinearRado](../D5/S3/Combinatorics/Matroids/LinearRado.lean) and [QTransversalRepresentability](../D5/S3/Combinatorics/Matroids/QTransversalRepresentability.lean), with their corresponding Blueprint Scribes. The result node displays the complete proposition and carries one `OpenProblemResolutionClaim` with kind `Proved`.

`LinearRado` has `admission_basis: escape-witness`, witnessed by the quotient induction in `linear_rado_finset`. The settling module has `admission_basis: open-problem-resolution (#19965; Proved)`. Both have `utility: none`; neither contains a fixed numerical certificate.

The escape audit is unfinished under [#22087](https://github.com/the-omega-institute/trureturing/issues/22087). Its four targets are `LinearRado.spanning_representatives`, `LinearRado.exists_nonsingular_rows`, `LinearRado.independent_support_matching` and `QTransversalRepresentability.result`, under the namespace `D5.S3.Combinatorics.Matroids`. No retained Reg registration or `declared_validated` status is claimed. The missing evidence is a faithful source-specific dependent-family reconstruction bridge, actual positive law, whole-family variation, sensitivity and observational dependence for an enrolled readout.

### Finite experiment

The experiment is in [trureturing-experiments at `1719af1a828bc229563613daf905c8790c446f20`](https://github.com/the-omega-institute/trureturing-experiments/tree/1719af1a828bc229563613daf905c8790c446f20/docs/reports/saaltink-2025-q-transversal-representability). The command `git -C /Users/auric/trureturing-experiments show 1719af1a828bc229563613daf905c8790c446f20:docs/reports/saaltink-2025-q-transversal-representability/check.py | python3` exits 0. The script SHA-256 is `227444b1b7c49b520349cb378544842c0132d02b5e2e028fd88dd3de85008ac7`.

The exact tested scope is six sampled families with $(m,k)=(3,3)$ over $\mathbb F_2$, checking all 16 subspaces each, and three sampled families with $(m,k)=(4,2)$, checking all 67 subspaces each. For these families, Definition 14 agrees with Theorem 18 and the constructed matrix satisfies the rank equality on every subspace. The tested extension degrees range from 6 to 24. These are computed finite checks; the universal statement is supplied by `result`.

## Triage

The completed proof is proposed for independent review and canonical implementation. The mathematical proof has no remaining probe obligation; the separate escape audit is unfinished under #22087.

| Item | Status | Evidence |
| --- | --- | --- |
| Conjecture 3 settlement and canonical mathematical assertion | Proved | Kernel-checked `QTransversalRepresentability.result` |
| Retained witness: one specialization preserves all required generic minors | Proved | Kernel-checked private `generic_minor_nonzero` and `specialized_independent_subspaces` |
| Mechanism: annihilating rows and simultaneous specialization | Proved | Kernel-checked private `specialized_independent_subspaces` and `qRank_eq_imageRank`; the route above describes their composition |
| Finite extension specified by polynomial degrees | Proved | Kernel-checked private `simultaneous_specialization_fin` and `finite_extension_primitive_degree`, with the choice described below |
| Uniform product bound $\prod_i(\operatorname{codim}X_i+1)$ and smaller sufficient degrees | Open | No delivered Lean statement proves this bound or optimality; the general finite-extension assertion does not assert it |
| Coordinate-family case of Theorem 24 | Proved in prose | Specialize `result` to coordinate subspaces; its quantifier over arbitrary families includes that subclass |
| Source Conjecture 1, the q-analogue of Rado's theorem | Open | Separate source question; the classical linear Rado lemma here is not Conjecture 1 |
| Source Conjecture 2, uniqueness of minimal presentations | Open | No delivered statement addresses presentation uniqueness |
| Definition 14 versus Theorem 18 in the sampled families | Computed | The experiment above: six $(3,3)$ families and three $(4,2)$ families, all their subspaces, exit 0, stated immutable script and SHA-256 |
| Rank equality for the sampled explicit matrices | Computed | The same experiment and scope, with extension degrees 6 through 24, exit 0 |
| Mathematical novelty and publication priority | Open | Literature reading: linear Rado and Kronecker substitution are established methods; this is a formal proof of the stated conjecture, with literature completeness `ASSUMED-UNVERIFIED` |

### What the settlement shows

**Proved (kernel-checked):** one finite-dimensional extension $K/F$ and one $k\times m$ matrix represent the q-transversal rank on every subspace, for every finite base field and arbitrary finite subspace family. The decisive mechanism is simultaneous preservation of selected generic minors, followed by the converse avoiding-matching argument and attainment of image rank.

**Proved (kernel-checked construction, without a sharp degree formula):** let $P$ be the finite nonzero minor family and let $Q$ be its univariate Kronecker images. The proof sets $D=1+\max_{q\in Q}\deg q$, with the finite supremum equal to zero for the empty set, and uses `FiniteField.Extension F p D` with an element of minimal-polynomial degree $D$. The weights are the mixed-radix prefix products of support-coordinate bounds. This describes the actual extension construction; it does not identify $D$ with the product bound in #19965.

**Proved in prose (scope):** the arbitrary-family conclusion includes the coordinate-family assertion of Theorem 24. Any source argument assuming only Conjecture 3's representation assertion can use this conclusion; no other source theorem is independently reproved here. Conjectures 1 and 2 and optimal extension degrees remain open.

## ASSUMED-UNVERIFIED

Literature-search completeness and publication priority are unverified beyond the screen recorded in #19965. The compiled proof establishes the literal rank representation claim, not a sharp universal extension-degree bound. The four-slot escape audit is unfinished under #22087. The finite experiment does not establish a uniform theorem beyond its stated sampled families.
