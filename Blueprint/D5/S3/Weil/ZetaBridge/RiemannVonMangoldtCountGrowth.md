# Riemann–von Mangoldt Zero-Count Growth

## Abstract

This node extracts the precise growth consequence required by the canonical `ZeroData` construction. For the repository's abstract zero configuration `Z`, a value

\[
h_{\mathrm{RvM}}:
\operatorname{RiemannVonMangoldt}(Z)
\]

contains the dyadic asymptotic

\[
N_Z(T,2T)
=
\frac{T}{2\pi}\ell_1(T)+O(\log T).
\]

The node proves that the main term dominates the logarithmic error for all sufficiently large `T`, and therefore

\[
N_Z(T,2T)\longrightarrow +\infty.
\]

## Main declarations

- `tendsto_l_atTop`
- `tendsto_T_mul_l_atTop`
- `dyadic_zero_count_eventually_ge`
- `dyadic_zero_count_tendsto_atTop`

## Role in the nonvacuity chain

The theorem is applied to `Zeta23.zetaZeroConfig`, whose carrier is exactly the set of nontrivial zeta zeros. An unbounded multiplicity-weighted dyadic count cannot be supported on a finite carrier. This supplies the infinitude premise consumed by `ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite`.

The node does not construct a new zero-counting function and does not assume any zero exists separately. All growth enters through the explicit `RiemannVonMangoldt Z` source.
