# Canonical zeta Cayley `J`-unitarity

## Scope

For a represented zero `rho`, the canonical Cayley coefficient is

\[
c(\rho)=\frac{\rho-1}{\rho}.
\]

The same-height mirror satisfies

\[
c(1-\overline\rho)=\overline{c(\rho)}^{-1}.
\]

This identity is transported to the multiplicity-expanded zero Hilbert space.

## Main result

Let `U_Z` be the diagonal Cayley operator and `J_Z` the mirror fundamental symmetry. Then

\[
U_Z^*J_ZU_Z=J_Z.
\]

Equivalently, the mirror Krein form is preserved:

\[
[U_Z\psi,U_Z\phi]_{J_Z}
=
[\psi,\phi]_{J_Z}.
\]

The proof is coordinatewise. The coefficient relation gives

\[
\overline{c(\rho_n)}\,c(\rho_{M(n)})=1,
\]

and summing the pointwise inner-product identities yields the global operator law.

## Canonical instance

Specializing to `zetaZeroData` gives the parameter-free theorem

\[
U_\zeta^*J_\zeta U_\zeta=J_\zeta.
\]

## Interpretation

Functional-equation symmetry already guarantees conservation in the indefinite mirror metric. Ordinary Hilbert-space unitarity is the stronger critical-line condition handled by the existing Cayley criterion.

## Boundary

`J`-unitarity alone permits nontrivial negative sectors. The theorem does not imply ordinary unitarity or RH.

## Truth anchors

- `cayleyCoefficient_mirrorIndex`
- `cayleyCoefficient_conj_mul_mirror`
- `zeroCayleyOperator_preserves_mirrorKreinForm`
- `zeroCayleyOperator_j_unitary`
- `zetaZeroCayleyOperator_j_unitary`
