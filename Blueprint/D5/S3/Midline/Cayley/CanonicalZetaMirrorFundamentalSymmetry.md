# Canonical zeta mirror fundamental symmetry

## Scope

The same-height mirror on zero indices preserves analytic multiplicity. It therefore lifts to the multiplicity-expanded coordinate type

\[
\mathcal I_Z=\sum_{n:\mathbb N}\operatorname{Fin}(m_n)
\]

and to a surjective linear isometry

\[
J_Z:\ell^2(\mathcal I_Z)\to\ell^2(\mathcal I_Z).
\]

## Fundamental-symmetry laws

The lifted mirror is involutive:

\[
J_Z^2=I.
\]

It is self-adjoint in inner-product form:

\[
\langle J_Z\psi,\phi\rangle
=
\langle\psi,J_Z\phi\rangle.
\]

Together with the linear-isometry structure, these identities make `J_Z` a fundamental symmetry.

## Krein form and odd directions

Define

\[
[\psi,\phi]_{J_Z}=\langle\psi,J_Z\phi\rangle.
\]

For a coordinate moved by the mirror, antisymmetrizing its basis vector gives a nonzero vector `v_-` with

\[
J_Zv_-=-v_-,
\qquad
[v_-,v_-]_{J_Z}=-\lVert v_-\rVert^2<0.
\]

Thus every nonfixed mirror coordinate supplies an explicit strict negative direction.

## Canonical instance

The parameter-free `zetaZeroData` from PR #5065 produces `zetaMirrorFundamentalSymmetry` without an additional zero-data hypothesis.

## Boundary

This node constructs the indefinite geometry forced by zero reflection. It does not prove that a moved coordinate exists and does not prove RH.

## Truth anchors

- `mirrorCoordinatePerm_involutive`
- `mirrorCoordinatePerm_fixed_iff`
- `mirrorFundamentalSymmetry_inner_left`
- `mirrorOddPart_eigenvalue_neg_one`
- `mirror_odd_vector_strictly_negative`
