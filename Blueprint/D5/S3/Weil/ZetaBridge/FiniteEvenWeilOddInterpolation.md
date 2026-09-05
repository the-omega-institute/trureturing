# Finite Even Weil Odd Interpolation

## Abstract

A finite sign-separated family of conjugate spectral pairs admits arbitrary independent odd-channel values from scalar even Weil tests. The construction upgrades the repository's finite even Paley–Wiener interpolation theorem to an explicit linear synthesis map.

The resulting interpolation basis has Gram matrix

\[
-4\operatorname{diag}(m_i),
\]

so its spectral negative index is exactly the number of independently observable orbit channels.

## Finite orbit frame

A `FiniteEvenWeilOrbitFrame Z ι` records:

- one zero index for every finite channel \(i\in\iota\);
- off-line and non-self-conjugate conditions;
- a finite node set;
- an exact equivalence between two copies of \(\iota\) and the nodes;
- identification of those copies with \(\gamma_i\) and \(\overline{\gamma_i}\);
- the sign-separation hypothesis required by even finite interpolation.

For prescribed \(a_i\in\mathbb C\), the target values are

\[
\widehat g(\gamma_i)=a_i,
\qquad
\widehat g(\overline{\gamma_i})=-a_i.
\]

The reduced odd readout is therefore

\[
O_i(g)
=
\frac{\widehat g(\gamma_i)-
\widehat g(\overline{\gamma_i})}{2}.
\]

## Simultaneous interpolation

The frozen interpolation theorem provides one even test satisfying all prescribed node values. Hence

\[
\boxed{
\forall a:\iota\to\mathbb C,
\quad
\exists g,\ O_i(g)=a_i\text{ for every }i.
}
\]

The node then selects one coordinate test \(g_i\) for each standard basis vector and defines the explicit finite synthesis

\[
S(a)=\sum_i a_i g_i.
\]

Fourier–Laplace linearity proves

\[
\boxed{O_j(S(a))=a_j.}
\]

Thus \(S\) is a right inverse to reduced odd evaluation and is injective.

## Exact Gram matrix

Define the reduced odd sesquilinear form

\[
B^-(g,h)
=
-4\sum_i m_i\,
\overline{O_i(g)}O_i(h).
\]

For the chosen coordinate tests,

\[
\boxed{
B^-(g_i,g_j)
=
-4m_i\delta_{ij}.
}
\]

Therefore the concrete Gram matrix is

\[
G^-=-4\operatorname{diag}(m_i).
\]

Since every analytic multiplicity is positive,

\[
\boxed{
\operatorname{negIndex}(G^-)=|\iota|.
}
\]

Multiplicity determines the negative weight and robustness margin. It does not produce additional scalar observer coordinates.

## Exact odd-energy realization

For the synthesized test,

\[
E_{\mathrm{odd}}(S(a))
=
4\sum_i m_i|a_i|^2.
\]

This is the finite negative target used by the quantitative remainder theorem.

## Claim boundary

The frame carries the exact finite sign-separation and node-identification hypotheses. This node does not prove that every arbitrary finite collection of orbit labels automatically satisfies those hypotheses, and it does not control contributions from zeros outside the selected orbit family.

## Truth anchors

- `exists_even_weil_frame_interpolant`
- `exists_even_weil_odd_interpolant`
- `frameOddSynthesis_readout`
- `frameOddBasisTest_gram`
- `frameOddGram_negIndex`
- `frameOddSynthesis_orbitOddEnergy`
