# Tribonacci Trace Lattice

## Abstract

On the certified Tribonacci scan, the nonintegral discrete spectrum is a conjugate-pair trace lattice.

For the triangular window 1 <= v1 <= v2 <= 200, every deficit has absolute value strictly below 955/1000. Exactly 8,934 of the 20,100 pairs are nonintegral, and the exact ratio lies in the half-open rounding interval [0.4435, 0.4445), hence rounds to 44.4 percent. The cubic-code image of that same scan is exactly the frozen eight-point spectrum.

For each pair in the nonintegral scan, let w be its exact cubic deficit code evaluated at the upper non-Perron Tribonacci root. There is an integer k such that the real deficit equals k minus w plus its complex conjugate in parentheses: deficit = k - (w + conj(w)). Thus modulo the integers the deficit is the negative C/R trace of the genuinely distinct complex-conjugate pair.

The remaining conjunctions retain the structural contrast verbatim. On the quadratic side the expanding and contracting deficits agree and the deficit is integral. On the cubic side the characteristic cubic splits into the Perron factor and its quadratic cofactor, while one minus the Perron root is irrational, so the Perron root alone does not carry the trace. Their conjunction states that integrality is a privilege of the two-faced structure.

The numerical bound, count, percentage, spectrum, and trace-lattice identification are window-certificate statements. They make no claim about an unrestricted scan or all natural index pairs.

**Theorem 1.1 (PZG Remark 6.27: the Tribonacci trace lattice).**

$$\left(\forall v1 \in N, v2 \in N,\; \left(1 \le \mathit{v1} \land \left(\mathit{v1} \le \mathit{v2} \land \mathit{v2} \le 200\right)\right) \Rightarrow \left|\operatorname{tribonacciDeficit}\left(\mathit{v1}, \mathit{v2}\right)\right| < \frac{955}{1000}\right) \land \left(\left(\operatorname{card}\left(\mathit{tribonacciNonintegralScanPairs}\right) = 8934 \land \left(\frac{4435}{10000} \le \frac{8934}{20100} \land \frac{8934}{20100} < \frac{4445}{10000}\right)\right) \land \left(\operatorname{image}\left(\mathit{tribonacciDeficitCodeAt10}, \mathit{tribonacciScanPairs}\right) = \mathit{tribonacciScanSpectrum} \land \left(\left(\forall pair \in \operatorname{Prod}\left(N, N\right),\; \mathit{pair} \in \mathit{tribonacciNonintegralScanPairs} \Rightarrow \left(\exists k \in Z,\; \operatorname{tribonacciDeficit}\left(\operatorname{fst}\left(\mathit{pair}\right), \operatorname{snd}\left(\mathit{pair}\right)\right) = k - \operatorname{tribonacciConjugatePairTrace}\left(\operatorname{tribonacciDeficitCodeAt}\left(10, \operatorname{fst}\left(\mathit{pair}\right), \operatorname{snd}\left(\mathit{pair}\right)\right)\right)\right)\right) \land \left(\left(\forall v1 \in N, v2 \in N,\; \operatorname{deficit}\left(\mathit{v1}, \mathit{v2}\right) = \operatorname{deficitContraction}\left(\mathit{v1}, \mathit{v2}\right) \land \left(\exists z \in Z,\; \operatorname{deficit}\left(\mathit{v1}, \mathit{v2}\right) = z\right)\right) \land \left(\left(\left(\forall z \in C,\; z^{3} - z^{2} - z - 1 = \left(z - \mathit{tribonacciConstant}\right) \cdot \operatorname{conjugateCofactor}\left(z\right)\right) \land \operatorname{Irrational}\left(1 - \mathit{tribonacciConstant}\right)\right) \land \left(\left(\forall v1 \in N, v2 \in N,\; \operatorname{deficit}\left(\mathit{v1}, \mathit{v2}\right) = \operatorname{deficitContraction}\left(\mathit{v1}, \mathit{v2}\right) \land \left(\exists z \in Z,\; \operatorname{deficit}\left(\mathit{v1}, \mathit{v2}\right) = z\right)\right) \land \operatorname{Irrational}\left(1 - \mathit{tribonacciConstant}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/TribonacciTraceLattice.pzg_remark_6_27_tribonacci_trace_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This one declaration packages all thirteen independently projectable proposition leaves. Frozen scan and structural certificates are referenced; the new leaf is the integer-congruence identity for the complex-conjugate pair trace.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/TribonacciTraceLattice.pzg_remark_6_27_tribonacci_trace_lattice`
- Dependency: [D5/S3/Constants/Irrationality/CubicConjugateTrace](CubicConjugateTrace.md)
- Dependency: [D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate](TribonacciDeficitScanCertificate.md)
- Dependency: [D5/S3/Constants/Irrationality/TwoFacedPrivilege](TwoFacedPrivilege.md)
