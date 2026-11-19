# Unit-weight Parseval for the signed dyadic Möbius difference

## Abstract

Unconditional unit-weight Parseval for the literal signed dyadic Möbius difference.

Let μ be the ordinary arithmetic Möbius function. For real x > 1, S(x) is the finite weighted sum mobiusPartialSum from `D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence`. The natural-floor cutoffs give the signed difference by cancelling the common prefix.

$$
\begin{gathered}S\left(x\right)=\sum_{1\leq n\leq\lfloor x\rfloor_{+}}\,\frac{\mu\left(n\right)}{n}\\D\left(x\right)=S\left(x\right)-S\left(2x\right)=-\sum_{\lfloor x\rfloor_{+}<n\leq\lfloor2x\rfloor_{+}}\,\frac{\mu\left(n\right)}{n}\end{gathered}
$$

**Definition 1.1 (Mellin symbol and its value at zero).**

$$\forall s\in\mathbb{C},H\left(s\right)=\begin{cases}\log 2,&s=0\\\frac{(1-2^{s})(\zeta\left(s+1\right)^{-1}-1)}{s},&s\neq0\end{cases}$$

*Formalization.* `D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval.mobiusDyadicMellinSymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here s is complex and 2 to the power s means exp((log 2)s). Near zero, sζ(1+s) extends holomorphically with value 1. Therefore the reciprocal ζ(1+s)⁻¹ tends to 0, and (1−2ˢ)/s tends to −log 2. The product has removable value log 2 as a complex number.

**Theorem 1.2 (Integrability and Parseval at unit weight).**

$$\begin{gathered}(x\mapsto D\left(x\right)^{2}\,x^{-1})\in L^{1}\left((1,\infty), \mathrm{d}x\right) \land\\(\xi\mapsto\left\Vert H\left(2\pi i\xi\right)\right\Vert^{2})\in L^{1}\left(\mathbb{R}, \mathrm{d}\xi\right) \land\\\int_{(1,\infty)}\,D\left(x\right)^{2}\,x^{-1}\,\mathrm{d}x=\int_{\mathbb{R}}\,\left\Vert H\left(2\pi i\xi\right)\right\Vert^{2}\,\mathrm{d}\xi\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval.mobiusDyadicDifference_unitWeight_parseval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both L¹ assertions use Lebesgue measure on the displayed domains. The time density includes x⁻¹. The frequency integral uses dξ with angular frequency 2πξ, so the displayed equality has unit prefactor.

For Re(s) > 0, the half-line Mellin transform with kernel x⁻ˢ⁻¹ sends S to ζ(1+s)⁻¹/s. Centering S by subtracting 1 gives (ζ(1+s)⁻¹−1)/s. The centered sum vanishes on (1,2), so dilating it by 2 multiplies this transform by 2ˢ after changing variables. Subtracting the dilated transform gives the displayed symbol.

For δ > 0, the function of u given by exp(−δu)D(exp u) on u ≥ 0 and zero on u < 0 is in L¹ and L². Its Fourier transform with phase exp(−2πiuξ) is H(δ+2πiξ). Apply normalized Plancherel and take δ = 1/(n+1) down to zero. The squared time densities increase pointwise. On 0 ≤ δ ≤ 1 the squared symbol is dominated by C²(1+|2πξ|)⁻³ᐟ², which is integrable. Monotone convergence on the time side and dominated convergence on the frequency side give finite equal masses. The substitution x = exp u turns du into dx/x on x > 1.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval.mobiusDyadicDifference_unitWeight_parseval`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval.mobiusDyadicMellinSymbol`
- Dependency: [D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound](../../Arith/MoebiusLogarithmic/ReciprocalBound.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/LineFourier](../ZetaGamma/FormCore/LineFourier.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence](MobiusPartialSumL2Divergence.md)
- Narrative reference: [D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence](MobiusPartialSumL2Divergence.md)
