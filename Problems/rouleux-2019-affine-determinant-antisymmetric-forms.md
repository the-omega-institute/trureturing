---
slug: rouleux-2019-affine-determinant-antisymmetric-forms
bibkey: rouleux2019multimodeentanglement
doi: 10.48550/arXiv.1910.04790
url: https://arxiv.org/abs/1910.04790v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.result
---

# Rouleux's affine-determinant conjecture for alternating polynomials

## Problem

M. Rouleux, *Multimode entanglement for fermions*, arXiv:1910.04790v1 (2019), §3, "Affine antisymmetric forms in higher dimensions or of lower degree", states in `3fermiProc.tex`, lines 266–269:

> We conjecture that: (1) the affine determinant is
> the only non degenerate antisymmetric tensor $\omega$ on ${\bf C}^d$ of degree $d$,
> depending on $d+1$ variables, and: (2)
> there is no non trivial antisymmetric tensor on ${\bf C}^d$ of degree $d$, depending on more than $d+1$ variables.

The preceding discussion specifies "degree being understood as degree of homogeneity" (line 247) and uniqueness "up to a factor" (lines 264–265). Definition 3, lines 251–253, gives the determinant of the differences from the first point. The source and its conventions are described in [the literature note](../Library/Eigenstructure/rouleux2019multimodeentanglement.md).

Issue [#23528](https://github.com/the-omega-institute/trureturing/issues/23528) fixes the polynomial reading. For natural numbers $d,r$, write $X_{i,j}$ for coordinate $j$ of vector variable $i$, with $0\le i<r$ and $0\le j<d$, and let $f$ be a complex polynomial in these $rd$ coordinates. `IsAlternating f` means that renaming the vector indices by any permutation $\sigma$, while fixing coordinate indices, multiplies $f$ by $\operatorname{sign}(\sigma)$. No multilinearity is assumed. Write $D_d=\texttt{affineDet}\ d$ for the polynomial whose evaluation is $\det(x_1-x_0,\ldots,x_d-x_0)$.

The four conjuncts of `result` establish:

1. For every $d,r$ with $r\ge d+2$, every alternating $f$ of total degree at most $d$ is zero.
2. For every $d$, $D_d$ is alternating and has total degree at most $d$.
3. For every $d$, every alternating $f$ in $d+1$ vector variables of total degree at most $d$ is $cD_d$ for some $c\in\mathbb C$.
4. For every $d\ge2$, the evaluated $D_d$ is non-degenerate: for every family $x_1,\ldots,x_d\in\mathbb C^d$, if $D_d(x_0,x_1,\ldots,x_d)=0$ for every $x_0\in\mathbb C^d$, then the direction of the affine span of $x_1,\ldots,x_d$ has complex dimension at most $d-2$.

This proves the preregistered polynomial reading of the two clauses. The total-degree hypothesis includes homogeneous degree-$d$ polynomials; the non-degeneracy statement has the explicit restriction $d\ge2$.

## Motivation

Rouleux (2019), arXiv:1910.04790v1, uses the affine determinant as an algebraic representation of $d+1$ fermionic inputs in $\mathbb C^d$ and uses it to define affine Slater determinants in §4. The conjecture asks whether antisymmetry and degree force this algebraic choice, and whether another vector variable is possible at the same degree. The settlement identifies the polynomial constraint underlying that construction; its physical interpretation requires additional structure.

## Gap

The bounded literature check in #23528 records:

- the source's two-clause conjecture in arXiv:1910.04790v1; the arXiv record lists only v1 and no journal reference;
- one citing work found through Semantic Scholar, Jeudy–Rouleux, arXiv:2411.03952, which the preregistration reports as listing the source in its bibliography without treating affine determinants or antisymmetric forms;
- arXiv searches for the exact title and for Rouleux with fermions, antisymmetric or determinant, the HAL record, and web searches for the conjecture, with no settlement found;
- repository searches reporting no existing treatment of arXiv:1910.04790, and distinguishing the already recorded Jeudy–Rouleux problem.

`not-found-in-searched-scope`. The classical alternant principle is relevant prior art; the bounded search does not establish originality of that principle or exhaustive priority for its application here.

## Route

For a monomial exponent array $m$, let $|m|$ be the sum of all its entries, with one row in $\mathbb N^d$ for each vector variable. The following are the module's private proof lemmas.

1. **Coefficients and repeated rows.** For any $d,r$, alternating complex polynomial $f$, permutation $\sigma$ of the $r$ vector indices and exponent array $m$, `coeff_permuted` relates the coefficient at the permuted array to $\operatorname{sign}(\sigma)$ times the coefficient at $m$. For alternating $f$, an arbitrary $m$, and distinct indices $a\ne b$ whose rows agree in every coordinate, `equal_rows_coeff_zero` gives $\operatorname{coeff}_m(f)=0$: swapping those rows fixes the monomial and negates its coefficient. Consequently, for alternating $f$ and $m$ in its support, `support_rows_distinct` makes its rows pairwise distinct.
2. **Too many variables.** For any $d,r$ and exponent array $m$ with pairwise distinct rows, `row_count_bound` gives $r\le |m|+1$: at most one row is zero and every other row contributes at least one. For $r\ge d+2$, alternating $f$ and $f.\operatorname{totalDegree}\le d$, `too_many_rows` applies this bound to every supported monomial and concludes $f=0$.
3. **The determinant.** For every natural $d$, `bordered_det` identifies $D_d$ with the determinant of the coordinate matrix with a row of ones adjoined. Permuting the points permutes its columns, giving `affineDet_alternating d`. Expanding the determinant of differences gives `affineDet_degree d`, the bound $\operatorname{totalDegree}(D_d)\le d$. These lemmas impose no positive-dimension hypothesis.
4. **One coefficient determines the polynomial.** For an exponent array on $d+1$ vector indices with pairwise distinct rows and $|m|\le d$, `distinct_rows_orbit` puts $m$ in the permutation orbit of `canonical d`, whose rows are zero and the $d$ coordinate unit vectors. For every natural $d$, `affineDet_coeff` gives coefficient one at `canonical d` in $D_d$. For alternating $f$ in $d+1$ vector variables with total degree at most $d$, `coefficient_determines` therefore gives $f=\operatorname{coeff}_{\texttt{canonical}\ d}(f)D_d$.
5. **Non-degeneracy.** For $d\ge2$, `affineDet_nondegenerate` proves the fourth conjunct. Given $d$ points and vanishing for every first point, assume those $d$ points are affinely independent. Their affine span is proper in $\mathbb C^d$, so a point $x_0$ outside it extends them to $d+1$ affinely independent points. The differences from $x_0$ are linearly independent and have nonzero determinant, contradicting the vanishing hypothesis. The affine-span direction consequently has dimension at most $d-2$.

## Falsifier

The settlement would miss the source if its variable action, degree or non-degeneracy condition differed from the preregistered reading. The formalization uses:

- complex coordinate polynomials, with simultaneous total degree at most $d$ and alternation under all permutations of the vector arguments;
- the determinant of the $d$ columns $x_k-x_0$, without imposing linearity in each of the $d+1$ arguments;
- `IsNondegenerate`, which quantifies over every family of $d$ fixed points and every possible first point, and bounds the direction dimension of their affine span.

The first three conjuncts include $d=0$ and $d=1$; the non-degeneracy conjunct requires $d\ge2$. At $d=0$ the determinant is the empty determinant. The translation from the source's tensor terminology and its exact-dimension wording to these definitions is discussed below as an argument rather than an additional Lean statement.

## Evidence

The canonical source is `D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.lean`.

- **Proof.** It proves `result`, the conjunction of vanishing, alternation and degree, scalar classification, and non-degeneracy stated above.
- **Reuse.** It reuses `D5.S3.Arith.Lattices.CofactorKernel.augment` for the bordered matrix and mathlib's polynomial, determinant and affine-independence results.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms.lean.json`.

Declaration statements:

- `result`: `sha256:c4d8226e24856610c0fd4a10ed3da9808992f10e2c5bd1956965a0ed6329a39c`.

## Triage

Tier 1 conjecture of a 2019 conference contribution, preregistered in issue #23528 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all natural $d,r$ with $r\ge d+2$, every alternating complex coordinate polynomial of total degree at most $d$ is zero; for every natural $d$, the affine determinant in $d+1$ vector variables is alternating with total degree at most $d$, and every alternating polynomial in those variables with that degree bound is a complex scalar multiple of it; for $d\ge2$, vanishing of the evaluated affine determinant for every first point forces the remaining $d$ points' affine-span direction to have dimension at most $d-2$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive mechanism and scope.* For alternating $f$ in $d+1$ vector variables of total degree at most $d$, `coefficient_determines` identifies its scalar with its coefficient at `canonical d`. Neither non-degeneracy nor homogeneity is a hypothesis of this lemma. Thus the classification already covers inhomogeneous polynomials satisfying the degree bound, including degenerate forms.
- *Non-degenerate scalar multiples.* For $d\ge2$, multiplication by $c\ne0$ preserves the vanishing condition, so $cD_d$ is non-degenerate. The zero form is degenerate: take the $d$ standard basis points, whose differences from one of them are $d-1$ linearly independent vectors; their affine-span direction has dimension $d-1>d-2$, although the zero form vanishes for every first point. Together with classification this gives exactly the nonzero scalar multiples for $d\ge2$. The restriction matters: for $d=1$ the affine span of the single remaining point has direction dimension zero, so `IsNondegenerate` also accepts the zero form.
- *The source's dimension wording.* For $d\ge2$ the $d$ remaining points form a nonempty set. If their affine-span direction has dimension at most $d-2$, extend a basis of that direction to $d-2$ vectors in $\mathbb C^d$ and translate the resulting subspace through one of the points. This gives a containing affine subspace of dimension exactly $d-2$, as in the source; the converse follows by inclusion of directions.
- *Sharpness and a degree boundary.* For every natural $d$, the affine determinant takes value one at $x_0=0$, $x_{k+1}=e_k$ for $0\le k<d$, so $d+1$ vector variables are attainable. Each product in its determinant expansion is homogeneous of degree $d$; the nonzero evaluation ensures that the resulting polynomial is nonzero of degree $d$. For $d\ge1$, multiplying $D_d$ by the symmetric linear polynomial $\sum_{i=0}^d X_{i,0}$ gives an alternating polynomial of degree $d+1$. It cannot be a constant multiple of $D_d$: the polynomial ring is an integral domain, $D_d$ is nonzero, and cancellation would make that nonconstant linear polynomial constant. Thus increasing the degree bound by one already destroys the scalar classification.
- *Tensor interpretation.* For a polynomial with values in any finite-dimensional complex vector space, choose a basis. If the polynomial is alternating and each coordinate has total degree at most $d$, apply the scalar statements to each coordinate: for $r\ge d+2$ all coordinates vanish, and for $r=d+1$ the polynomial is $D_d$ times a fixed target vector. In particular, the source's top exterior power $\Lambda^d\mathbb C^d$ is one-dimensional, with basis $e_1\wedge\cdots\wedge e_d$, so its polynomial-valued reading reduces to the scalar one. The coordinate representation and exterior-power identification are not formalized in this module.
- *Effect on the paper and neighbouring questions.* Rouleux's §4 defines its affine Slater determinant directly using the determinant of differences (Definition 4, lines 299–301). The settlement supplies uniqueness of that universal alternating polynomial recipe, at the stated degree, when its vector arguments vary independently. The subsequent overlap and density-matrix formulas concern the selected recipe and receive no analytic verification from this theorem. The separate collapse conjecture in §3, lines 271–272, still requires a construction analogous to Proposition 2 in higher dimension; uniqueness of a polynomial does not construct that collapse map. The lower-degree partial affine determinants in lines 274–277 are outside this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded to the searches recorded in #23528 and does not establish exhaustive worldwide novelty or priority. Its Semantic Scholar citation search, arXiv API searches, HAL reading, repository searches and reading of Jeudy–Rouleux (arXiv:2411.03952) have not been independently reproduced here. The source conjecture and its surrounding definitions were checked directly in Rouleux's arXiv:1910.04790v1 TeX, and the arXiv abstract record supplies the DOI and version metadata.

Everything in "Argued, not formalized" goes beyond the exact type of `result`: the scalar non-degeneracy criterion and its low-dimensional boundary, the exact-dimension translation, the sharpness examples, the tensor-coordinate bridge and the interpretation of the source's later constructions. The theorem assumes complex coordinate polynomials; other readings of antisymmetric tensor require their own representation bridge. The higher-dimensional collapse conjecture, lower-degree classification, physical realization, and the source's analytic and density-matrix calculations are not settled by this module.
