# Off-Line Orbit Parity Decomposition

## Abstract

Every supplied nonreal off-line four-point zero orbit splits into a nonnegative even spectral energy minus a nonnegative odd spectral correction.

**Theorem 1.1 (Off-line orbit parity decomposition).**

Let \(Z\) be supplied zero data, \(g\) a Weil test function, and \(n\) an index whose zero is nonreal and off the critical line. Put

\[
A=\widehat g(\gamma_n),\qquad
B=\widehat g(\overline{\gamma_n}),
\]

\[
A_{\mathrm{even}}=rac{A+B}{2},\qquad
A_{\mathrm{odd}}=rac{A-B}{2}.
\]

Define

\[
E_{\mathrm{even}}=4m_n\lvert A_{\mathrm{even}}vert^2,\qquad
E_{\mathrm{odd}}=4m_n\lvert A_{\mathrm{odd}}vert^2.
\]

Then the real contribution of the four-point orbit is

\[
oxed{
Q_{\operatorname{orb}(n)}(g)
=E_{\mathrm{even}}-E_{\mathrm{odd}}.
}
\]

Moreover,

\[
E_{\mathrm{even}}\ge0,\qquad E_{\mathrm{odd}}\ge0,\qquad
Q_{\operatorname{orb}(n)}(g)+E_{\mathrm{odd}}=E_{\mathrm{even}}.
\]

*Proof.* Machine-checked in Lean as `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition`.

*Source.* Repository-derived.

*Commentary.*

Complex-frequency convolution-square factorization gives the orbit term \(4m_n\operatorname{Re}(A\overline B)\). The identity

\[
\operatorname{Re}(A\overline B)
=\left\lvertrac{A+B}{2}ightvert^2
-\left\lvertrac{A-B}{2}ightvert^2
\]

isolates the full sign-indefinite part in the odd channel. The odd energy is independently constructed from the antisymmetric spectral evaluation and supplies a canonical positive completion of the orbit contribution.

The theorem assumes supplied `ZeroData`; it makes no existence claim for an off-line zero and no Riemann-hypothesis conclusion.

## References

- Truth anchor: `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.off_line_orbit_parity_decomposition`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds](../ZetaBridge/ConvolutionSquareOrbitBounds.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits](../ZetaBridge/ConvolutionSquareOffLineOrbits.md)
