# Finite mirror Krein index

## Scope

Every symmetric spectral-radius window is finite and stable under the same-height mirror. For each nonfixed two-point mirror orbit, this node selects the smaller natural-number index as its presentation representative and allocates one odd coordinate for every analytic-multiplicity copy.

## Finite index

Let

\[
\mathcal R_T
=
\{n\in S_T:n<M(n)\}.
\]

Define

\[
\kappa_T
=
\sum_{n\in\mathcal R_T}m_n.
\]

This counts each nonfixed mirror pair once, weighted by analytic multiplicity.

## Exact negative sector

The odd-coordinate type is

\[
\mathcal I_T^-
=
\sum_{n\in\mathcal R_T}\operatorname{Fin}(m_n).
\]

The node proves

\[
\#\mathcal I_T^- = \kappa_T.
\]

On functions `v : I_T^- -> C`, define

\[
Q_T^-(v)=-\sum_i|v_i|^2.
\]

Then

\[
v\ne0\Longrightarrow Q_T^-(v)<0.
\]

Thus `kappa_T` is the exact dimension of an explicitly constructed strictly negative finite sector.

## Critical-line criterion

The following conditions are equivalent:

\[
\kappa_T=0,
\]

\[
M(n)=n\quad\text{for every }n\in S_T,
\]

\[
\operatorname{Re}\rho_n=\frac12
\quad\text{for every }n\in S_T.
\]

Moreover, `kappa_T > 0` exactly when the window contains an off-line zero.

## Boundary

The integer `kappa_T` counts the explicitly constructed mirror-odd sector. Identifying it with the negative eigenvalue count of another sampled Gram or Weil matrix requires a separate full-rank transport theorem.

## Truth anchors

- `mirrorPairRepresentatives_eq_empty_iff`
- `finite_mirror_krein_index_zero_iff_critical`
- `finiteMirrorKreinIndex_pos_iff_exists_offLine`
- `mirrorOddCoordinate_card`
- `finiteMirrorOddQuadratic_strictly_negative`
- `finite_mirror_krein_index_spec`
