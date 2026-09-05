# Quantitative Multi-Orbit Weil Negative Certificate

## Abstract

The finite interpolation layer produces an exact negative target quadratic on a space of independently observable orbit channels. This node proves that a single uniform quadratic remainder bound below the least target weight preserves strict negativity on the whole coefficient space.

The conclusion is an injective finite-dimensional family of admissible Weil tests whose full multiplicity-weighted zeta zero sums are strictly negative.

## Generic perturbation theorem

For \(a:\iota\to\mathbb C\), define

\[
\|a\|_2^2=\sum_i|a_i|^2
\]

and a weighted negative target

\[
Q_0(a)=-\sum_iw_i|a_i|^2.
\]

Suppose

\[
0<m\le w_i
\]

for every \(i\), and the full form decomposes as

\[
Q(a)=Q_0(a)+R(a)
\]

with

\[
|R(a)|\le\varepsilon\|a\|_2^2,
\qquad
\varepsilon<m.
\]

Then every nonzero vector satisfies

\[
\boxed{Q(a)<0.}
\]

The proof controls the full quadratic remainder uniformly. Pointwise estimates on individual basis vectors would not suffice because cross terms could destroy negativity on linear combinations.

## Weil specialization

For a finite observable orbit frame, the exact target is

\[
Q_{\mathrm{target}}(a)
=
-4\sum_i m_i|a_i|^2.
\]

The actual full zero-side quadratic is

\[
Q_{\mathrm{full}}(a)
=
\operatorname{Re}\operatorname{zeroSum}
\left(
Z,
S(a)*\widetilde{S(a)}
\right),
\]

where \(S\) is the explicit finite odd synthesis. The remainder is defined exactly by

\[
R(a)=Q_{\mathrm{full}}(a)-Q_{\mathrm{target}}(a).
\]

A `QuantitativeMultiOrbitCertificate` contains:

- a positive multiplicity floor \(m_*>0\);
- \(m_*\le m_i\) for every selected orbit;
- a uniform bound
  \[
  |R(a)|\le\varepsilon\|a\|_2^2;
  \]
- the strict margin condition
  \[
  \varepsilon<4m_*.
  \]

The node proves

\[
\boxed{
 a\ne0
 \Longrightarrow
 Q_{\mathrm{full}}(a)<0.
}
\]

It also proves that the synthesis is injective, so different coefficient vectors produce different bundled test functions.

## Mathematical role

This statement converts finite exact interpolation into a robust negative-subspace certificate. The remaining analytic work is isolated in one independently auditable predicate, `HasUniformMultiOrbitRemainderBound`.

The required bound must account jointly for all unselected zeros and all cross terms. It is stronger than proving a negative witness one orbit at a time.

## Claim boundary

This node does not prove the uniform remainder estimate itself. Existing closed-strip decay, convolution-power amplification, absolute zero summability, and the explicit formula are intended inputs for that next analytic construction.

## Truth anchors

- `strictNegative_of_uniformQuadraticRemainder`
- `frameOddSynthesis_injective`
- `frameOddTargetQuadratic_le_massFloor`
- `quantitativeMultiOrbit_strictly_negative`
- `quantitative_multiOrbit_weil_negative_certificate`
