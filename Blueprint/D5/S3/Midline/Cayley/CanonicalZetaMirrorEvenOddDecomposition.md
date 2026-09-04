# Canonical Zeta Mirror Even-Odd Decomposition

## Abstract

The same-height mirror is an involutive self-adjoint isometry on the multiplicity-expanded zero Hilbert space. This node constructs its normalized even and odd projections and proves their full spectral-projection algebra.

## Main identities

\[
P_+=\frac{I+J}{2},
\qquad
P_-=\frac{I-J}{2}.
\]

The node proves

\[
P_+^2=P_+,
\quad
P_-^2=P_-,
\quad
P_+P_-=P_-P_+=0,
\quad
P_++P_-=I,
\]

as vector identities, together with Hilbert orthogonality of the two ranges. The mirror Krein form then has the exact energy decomposition

\[
[\psi,\psi]_J
=\|P_+\psi\|^2-\|P_-\psi\|^2.
\]

Thus the negative sector is the actual mirror-odd spectral subspace rather than an auxiliary sign convention.

## Truth anchors

- `mirrorEvenPart_idempotent`
- `mirrorOddProjectionPart_idempotent`
- `mirrorOddProjectionPart_eq_zero_iff`
- `mirror_even_odd_inner_eq_zero`
- `mirrorKreinForm_even_odd_decomposition`
- `canonical_mirror_even_odd_decomposition`
