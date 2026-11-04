---
slug: kaygorodov-martin-gonzalez-viruel-2026-hilbert-natural-basis-uniqueness
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness
---

# Natural orthonormal bases of a dense-square Hilbert evolution algebra

## Problem

Kaygorodov, Martin Gonzalez and Viruel, *Evolution algebras: a survey of
results and a list of open problems*, arXiv:2610.22248v1, section 2.2.8,
Question 46 (page 26), ask:

> If the square of a Hilbert evolution algebra is dense, is its natural
> orthonormal basis unique up to permutation and unimodular scalars?

The assertion quantifies over real or complex complete separable Hilbert
spaces, bilinear products with bounded left multiplication for every fixed
vector, and two complete natural orthonormal bases indexed by the positive
integers. The algebraic square is the linear span of all pair products;
density means norm density. Completeness of a basis means closed linear
span equal to the Hilbert space. The following sentence about derivations,
automorphisms and spectral theory is excluded.

## Motivation

The condition that all products span densely need not distinguish individual
basis squares. A pair of equal nonzero squares can retain an orthonormal
rotation while the remaining squares generate a dense subspace. The
interaction between these two facts is the source of nonuniqueness.

## Gap

The Hilbert realization framework is in arXiv:2012.05124v2, Definition 2.2
and Corollary 2.4. The algebraic table is Example 3.7 of arXiv:2505.14584v1.
The equal-square rotation mechanism is in arXiv:2311.08387v2, Examples
3.6-3.7. These are credited ingredients. The latter examples alone have
square in a proper closed coordinate hyperplane and do not provide a dense
square. Combining the table, complete Hilbert realization, dense product
span and complete nonmonomial natural basis is the assertion considered here.

## Route

Take $H=\ell^2(\mathbb N_{>0},\mathbb C)$ and its standard Hilbert basis
$(e_i)$. Define the complex-bilinear product on all of $H\times H$ by
\[
 \mu(x,y)=x_1y_1e_1+\sum_{i\ge2}x_iy_ie_{i-1}.
\]
The uniformly bounded coordinate bilinear maps and the two-two Holder
pairing give a norm-convergent series and a continuous bilinear map.
For each $v$, the strictly positive constant $\|\mu(v,\cdot)\|+1$ is a
left-multiplication bound for every $w$.

The table is $e_1^2=e_2^2=e_1$ and $e_{i+1}^2=e_i$, with zero mixed
products. Put
\[
 f_1=\tfrac35e_1+\tfrac45e_2,\qquad
 f_2=-\tfrac45e_1+\tfrac35e_2,\qquad f_i=e_i\quad(i\ge3).
\]
The block and its inverse preserve orthonormality and closed span. Equality
of the first two squares cancels the only potentially nonzero mixed
product in the changed block. Every $e_i$ is a square, so the algebraic
product span is norm dense. The vector $f_1$ has two nonzero standard
coordinates and cannot be a scalar multiple of any single $e_j$.
Thus every permutation and every unimodular scalar family fails at index
one. A complex counterexample refutes the real-or-complex universal claim.

## Falsifier

A failure of complete orthonormality, norm convergence, bilinearity, a
left-multiplication bound, naturality for either full basis, norm density of
the algebraic square, or the exclusion of any proposed identification would
invalidate the counterexample. Replacing a Hilbert basis by a finite or
Hamel basis, or postulating density or continuity, would not establish this
assertion.

## Evidence

The formal endpoint is
`D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result`.
Its literal type is the negation of `claim`. The definition `claim` is the
conjunction of the real and complex universal uniqueness assertions.
The proof uses the stronger complex counterexample. The accepted axiom
boundary is the closure contained in `propext`, `Classical.choice` and
`Quot.sound`. The public definitions `e`, `mu` and `f` over the explicit `lp` carrier
identify the complete witness; the private analytic and coordinate arguments discharge
all its hypotheses.

## Triage

### What the settlement shows

- Proved: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result`
  refutes the whole first interrogative for the stated real-or-complex class
  by a complex counterexample. The complex universal assertion is a
  consequence of the full conjunction, not an equivalent reformulation.
- Proved within that result: the equal nonzero first two basis squares
  permit the displayed orthogonal block. Bilinearity cancels its mixed
  product, while every standard vector remains a square. This is the
  mechanism by which norm density coexists with distinct complete natural
  orthonormal bases; it is not a separate theorem or additional resolution.
- Computed: no numerical or finite-search conclusion is used. The rational
  coefficients are exact, and the infinite-dimensional analytic premises
  are discharged in the Lean proof.
- Surviving boundary: the result refutes uniqueness from dense square alone;
  it supplies no uniqueness theorem under additional independence hypotheses
  on basis squares. That strengthened direction remains open here.
- Effect: a claim relying on uniqueness cannot obtain that premise solely
  from density of the algebraic square. The present result does not classify
  derivations, automorphisms or spectra; the next sentence of Question 46
  remains open here, and no other survey question is included.
- Eligible successor: none is established or selected. The independence
  direction above has no separately verified external question or complete
  admission basis in this unit and receives no separate problem count.

## ASSUMED-UNVERIFIED

The bounded source and literature checks identified no prior published
whole answer. Citation closure and semantic coverage of all literature
remain incomplete because of citation-service rate limits and indexing
limitations. No global absence, construction-discovery or priority claim
is made. The algebraic table, Hilbert realization and equal-square rotation
method are attributed to their existing sources.
