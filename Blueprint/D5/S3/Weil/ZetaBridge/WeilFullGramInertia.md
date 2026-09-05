# Actual Full Weil Gram Inertia

Status: Candidate Lean source and author projection. Source delivery does not imply pinned kernel verification or repository admission.

Let W(g,h) be the complete absolutely convergent zero sum of convolve(g, involution(h)). Define the actual matrix by G(i,j)=W(basis(j),basis(i)), using the standard conjugate-linear row convention.

The existing same-height mirror permutation preserves analytic multiplicity and conjugates the spectral parameter. Reindexing the complete sum therefore proves G is Hermitian. Absolute summability of every mixed term justifies the exact identity

`star(a) dot (G mulVec a) = zeroSum(convolutionSquare(sum_i a_i basis_i))`.

The common Burnol construction already supplies one actual finite basis with injective synthesis and a strictly negative full Weil square for every nonzero complex coefficient vector. The new source transports that result to PosDef(-G), then uses the repository spectral RHLinalg.negIndex and Mathlib positive-definite eigenvalue theorem to prove

`negIndex(G) = Fintype.card(orbit channels)`.

The full matrix is not asserted to equal its finite target diagonal. All infinite-tail cross terms remain in its actual entries. The theorem is about the matrix produced by actual test functions, rather than an abstract replacement matrix of the same size.

A valid finite separated nonreal off-line orbit frame remains an input. Empty frames give the zero-dimensional case. No existence of off-line zeros, RH, equality with the multiplicity-expanded ambient index, computable uniform localization depth, or fixed support window across all frames is claimed.

Main declarations: fullMixedWeilForm_conj; fullWeilGram_isHermitian; fullWeilGram_quadratic; neg_fullWeilGram_posDef_of_strictNegative; fullWeilGram_negIndex_of_strictNegative; exists_actual_full_weil_gram_with_exact_negative_index.

Library interfaces checked against Mathlib tag v4.33.0: Matrix.PosDef.of_dotProduct_mulVec_pos, Matrix.IsHermitian.im_star_dotProduct_mulVec_self, Complex.pos_iff. The eigenvalue-to-index step directly reuses the repository pattern in FiniteMirrorKreinGramInertia.
