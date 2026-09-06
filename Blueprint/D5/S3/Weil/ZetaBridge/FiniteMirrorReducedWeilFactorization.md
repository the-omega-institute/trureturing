# Finite Mirror-Reduced Weil Factorization

## Abstract

The finite convolution-square zero sum factors exactly through the scalar observer's reflection-reduced space. One coordinate is retained per distinct zero, and analytic multiplicity is kept as a positive weight in the form.

The node also aggregates the existing one-orbit parity decomposition over an arbitrary finite family of off-line nonreal four-point orbit blocks.

## Reduced observable space

For the finite window

\[
I_T=\{n:n\in Z.\operatorname{symmetricIndices}(T)\},
\]

let `FiniteReflectionEvenVector Z T` be the subtype of vectors satisfying

\[
v(R(n))=v(n).
\]

A Weil test defines the reduced vector

\[
v_g(n)=\widehat g(\gamma_n).
\]

The finite same-height mirror is

\[
M(n)=C(R(n)),
\]

and the multiplicity-weighted reduced form is

\[
B_T(v,w)
=
\sum_{n\in I_T}m_n\,v(n)\overline{w(M(n))}.
\]

## Exact factorization

For every bundled Weil test,

\[
\boxed{
\operatorname{truncatedZeroSum}
  (Z,g*\widetilde g,T)
=
B_T(v_g,v_g).
}
\]

The proof uses the established complex-frequency identity

\[
\widehat{g*\widetilde g}(z)
=
\widehat g(z)\overline{\widehat g(\overline z)}
\]

and the stored same-height mirror relation

\[
\gamma_{M(n)}=\overline{\gamma_n}.
\]

No square-root multiplicity factor is introduced, so multiplicity is counted exactly once.

## Finite orbit parity aggregation

For a finite family of indices representing nonreal off-line four-point orbits, define

\[
Q_{\mathrm{block}}
=
\sum_i Q_{\operatorname{orb}(i)},
\]

and sum the established channel energies. Then

\[
\boxed{
Q_{\mathrm{block}}
=
E_{\mathrm{even}}-E_{\mathrm{odd}},
\qquad
E_{\mathrm{even}},E_{\mathrm{odd}}\ge0.
}
\]

Disjointness is not required for this algebraic identity. It is required only when interpreting the block sum as a sum over the union of zero indices without repeated orbit contributions.

## Mathematical role

This is the exact bridge from actual finite zero sums to the observer-reachable quotient. It replaces the incorrect idea that scalar Weil tests act freely on every multiplicity-expanded coordinate.

## Claim boundary

The factorization is finite. It does not establish simultaneous interpolation, a negative index, an infinite zero-sum statement, or a uniform tail estimate. Those are separate downstream obligations.

## Truth anchors

- `zeroSummand_convolutionSquare_eq_reducedMirrorTerm`
- `truncatedZeroSum_convolutionSquare_eq_reducedMirrorForm`
- `truncatedZeroSum_convolutionSquare_re_eq_reducedQuadratic`
- `finite_offLine_orbit_block_factorization`
