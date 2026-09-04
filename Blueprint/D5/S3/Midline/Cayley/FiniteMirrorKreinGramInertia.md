# Finite Mirror Krein Gram Inertia

## Abstract

This node embeds one odd vector for every selected nonfixed mirror pair and every analytic-multiplicity copy into the actual multiplicity-expanded zero Hilbert space. It then forms the Gram matrix using the genuine mirror Krein form.

## Exact Gram computation

For the selected odd basis vectors `v_i^-`,

\[
[v_i^-,v_j^-]_J=-2\delta_{ij}.
\]

Hence the actual Gram matrix is

\[
G_T^-=-2I.
\]

Using the repository's Hermitian inertia owner `RHLinalg.negIndex`, the node proves

\[
n_-(G_T^-)
=
\sum_{n\in\mathcal R_T}m_n
=
\kappa_T.
\]

Therefore the spectral negative index of a concrete Gram matrix is positive exactly when the finite window contains an off-line mirror orbit. This upgrades the earlier coordinate-cardinality certificate to an actual matrix-inertia theorem.

## Truth anchors

- `mirrorOddVector_source_inner`
- `mirrorOddVector_source_krein`
- `finiteMirrorOddKreinGram_eq`
- `finiteMirrorOddKreinGram_negIndex`
- `finiteMirrorOddKreinGram_negIndex_pos_iff_exists_offLine`
- `canonical_zeta_finite_mirror_gram_inertia`
