---
bibkey: kaygorodov2026evolution
authors: Ivan Kaygorodov; Cándido Martín González; Antonio Viruel
year: 2026
title: "Evolution algebras: a survey of results and a list of open problems"
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
claim: "Conjecture 4 asks for the simple complex evolution-algebra automorphism maximum max{n!, n(2^n-1)}; Theorem 4 and Conjecture 3 concern perfect algebra automorphisms; Question 46 asks whether dense square forces uniqueness of a Hilbert natural orthonormal basis; Question 14 asks whether an infinite natural-basis quotient can coexist with finite full automorphisms."
strata_touched:
  - D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum
  - D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases
  - D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness
  - D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl
  - D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport
  - D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation
license: citation-only
triage: anchor
---

# Evolution algebra automorphisms and ordinary nilpotency

Multiplication is bilinear and may be nonassociative. Theorem 4 supplies
monomiality for perfect evolution algebras. Section 2.1.6 describes the diagonal
arrow equations. Section 2.3, Conjecture 3 asks for the maximum automorphism
order over all perfect complex evolution algebras of each positive dimension,
including attainment, six specified small values and the factorial tail.
Monomiality and finite diagonal groups are credited supporting results, not a
solution of this conjecture. The quotient-control bound does not assert the
sharp maximum, attainment or an exclusive extremizer classification.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2610.22248
- URL: https://arxiv.org/abs/2610.22248v1
- Text: https://arxiv.org/html/2610.22248v1
- Locations: Theorem 4; section 2.1.6 and Remark 19; section 2.3, Conjecture 3;
  Question 33 for the point-group sequence onto the permutation image.

The group-scheme sequence in equation (2) has no terminal surjectivity claim
onto the full graph automorphism group. The formal model uses the actual image
and the actual block-action kernel.

## Hilbert natural-basis uniqueness

Section 2.2.8, Question 46, page 26 asks: "If the square of a Hilbert evolution algebra
is dense, is its natural orthonormal basis unique up to permutation and
unimodular scalars?" Section 1.8 and the cited Hilbert evolution algebra
framework allow real or complex scalars, complete orthonormal natural bases,
and continuous left multiplication. Here the square is the algebraic span of
all pair products and density is norm density. The subsequent sentence about
bounded derivations, automorphisms and spectral theory is a separate request.
A complex counterexample refutes the first universal assertion for the full
real-or-complex class. The first interrogative is a question in this source,
not a theorem attributed to its authors.

## Natural bases with finite full automorphisms

Section 2.2.2, Question 14 asks: "Describe the set of natural bases (up to
permutation and scaling) of a non-degenerate evolution algebra. When is it
finite? Can it be infinite for an algebra whose automorphism group is finite?"
The selected assertion is the entire final sentence. Section 1.1 permits
an arbitrary field, assumes finite dimension unless otherwise stated, and
identifies nondegeneracy with zero annihilator. Aut denotes all field-valued
linear multiplication automorphisms. Complex scalars give a permitted
existence witness. Basis equivalence allows arbitrary permutations and
independent nonzero scalars, without quotienting by algebra automorphisms.

The two-dimensional algebra and its finite full group are prior ingredients
from arXiv:1807.02362v1 and arXiv:2303.00862v1. The Q14 endpoint combines
these with a separated infinite family in the exact basis quotient. It
does not answer the first two interrogatives or assert global priority.

## Ordinary nilpotency spectrum

Section 1.1 defines ordinary lower powers by A^1=A and
A^m=sum_{i=1}^{m-1} A^i A^{m-i}. The products are bilinear and need not
be associative or power-associative. Section 2.3, Conjecture 9 states that
over each infinite field an n-dimensional nilpotent evolution algebra of
index k+1 exists exactly when k=2^a for 0<=a<=n-1, or k has at least two
nonzero binary digits and floor(log_2 k)+s_2(k)<=n-1. A natural basis
requires zero mixed products; zero natural squares are allowed.

The fifteen-dimensional rational algebra in
`D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation`
has ordinary index 256. At k=255, the logarithm and binary digit count
are 7 and 8, whose sum exceeds 15-1. The construction and its proof
are project results, while the question and definitions are from this survey.

## Simple-algebra automorphism maximum

Conjecture 4, section 2.3, page 28 states: “Over ℂ, the maximal order of the
automorphism group of a simple n-dimensional evolution algebra is
max{n!, n(2ⁿ−1)}.” The dimension is positive. The same paragraph identifies the
cyclic product and generic complete-support products as attaining families.

The source's Theorem 6 uses simplicity in the usual ideal sense. Its cited
Cabrera Casado, Siles Molina and Velasco source, arXiv:1601.01832v2, section 4, page 18,
states: “We recall that an algebra A is simple if A² ≠ 0 and 0 is the only
proper ideal.” The formal predicate quantifies over every complex vector
subspace absorbing multiplication on both sides. The full group consists of
all complex linear multiplication automorphisms, without an associativity
or multiplicative-unit assumption.

The uniform maximum proof and the explicit I+J attaining family are
repository results. Strong connectivity makes the successor quotient one
cycle. A supported permutation gives equal positive quotient fibers. The
joint group bound reduces to h(2ʰ−1)(k!)ʰ with n=hk; the factorial comparison
and its boundary cases give the asserted maximum. Classification of all
extremizers and attainment over other fields remain open here.
