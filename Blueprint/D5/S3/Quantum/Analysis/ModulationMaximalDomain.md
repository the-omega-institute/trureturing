# Physical Modulation and Its Maximal Derivative Domain

## Abstract

Positive physical modulation has exactly the maximal coordinate multiplication domain in the actual L2 space.

**Definition 1.1 (Positive phase multiplication).**

$$\forall d \in \mathbb{N}, h \in \mathbb{R}, b \in \operatorname{E}\left(d\right), t \in \mathbb{R}, f \in \operatorname{H}\left(d\right),\; \operatorname{M}\left(h, b, t, f\right) = [x: \operatorname{E}\left(d\right) \mapsto \operatorname{exp}\left(\frac{i \cdot t \cdot \operatorname{inner}\left(b, x\right)}{h}\right) \cdot f\left(x\right)]$$

*Formalization.* `D5/S3/Quantum/Analysis/ModulationMaximalDomain.physicalModulation` (`✓ std3`).

*Citation.* Gerald Teschl (2009). *Mathematical Methods in Quantum Mechanics: With Applications to Schrodinger Operators*. URL: <https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf>.

*Commentary.*

For every natural number d, E(d) is EuclideanSpace Real (Fin d), with Lebesgue measure volume, and H(d) is Lp Complex 2 volume. The brackets denote the almost-everywhere L2 class of the displayed function. The inner product is the real Euclidean inner product, cast to Complex where it multiplies a complex value. M(h,b,t,f) denotes physicalModulation h b t f. The formula defines M for every real h, using the total field convention 1/0=0; when h is zero the displayed phase is one. Its derivative theorem assumes h positive, so the fractions there use ordinary division.

**Theorem 1.2 (Complete strong derivative graph).**

$$\forall d \in \mathbb{N}, h \in \mathbb{R}, b \in \operatorname{E}\left(d\right), f \in \operatorname{H}\left(d\right), v \in \operatorname{H}\left(d\right),\; 0 < h \Rightarrow (\operatorname{HasDerivAt}\left((t: \mathbb{R} \mapsto \operatorname{M}\left(h, b, t, f\right)), v, 0\right) \Leftrightarrow \left(\exists u \in \operatorname{MemLp}\left(\operatorname{Z}\left(b, f\right), 2, \mathrm{volume}\right),\; v = \frac{i}{h} \cdot \operatorname{toLp}\left(u, \operatorname{Z}\left(b, f\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ModulationMaximalDomain.physical_modulation_hasDerivAt_iff` (`✓ std3`). ∎

*Citation.* Gerald Teschl (2009). *Mathematical Methods in Quantum Mechanics: With Applications to Schrodinger Operators*. URL: <https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf>.

*Commentary.*

Here h is the positive Planck scalar hbar and i is Complex.I. Z(b,f) is the function x mapping to inner(b,x) times f(x). MemLp uses exponent two and volume. A witness u of MemLp(Z(b,f),2,volume) supplies toLp(u,Z(b,f)), namely u.toLp Z(b,f). The dot in the conclusion is complex scalar multiplication on H(d). HasDerivAt means the norm derivative with real time.

The phase derivative bounds each difference quotient by the norm of (i/h) Z(b,f). When Z(b,f) is in L2, the squared error is dominated by four times the squared norm of that function. Dominated convergence therefore proves convergence of the actual L2 difference quotients and gives the derivative.

Conversely, a strong derivative implies convergence of the quotient classes in L2 and hence in measure. A strictly increasing subsequence converges almost everywhere. Countably many representative equalities hold on a common set of full measure. Scalar derivative uniqueness identifies the limit with (i/h) Z(b,f). The derivative is in L2 and i/h is nonzero, so Z(b,f) is in L2.

All finite dimensions, including zero, and all directions, including zero, are included. Both f and v are arbitrary actual L2 vectors. The derivative side requires no finite-volume, global L1, Schwartz, or coordinate-product integrability assumption. Changing a representative on a null set preserves both the condition and its toLp class.

Teschl's maximal multiplication domain, equation (2.21), and the strong derivative characterization in Theorem 5.1(ii) give the literature correspondence. For the real multiplier A(x)=-inner(b,x)/h, the convention U(t)=exp(-itA) gives the positive phase and derivative (i/h) Z(b,f).

## References

- Truth anchor: `D5/S3/Quantum/Analysis/ModulationMaximalDomain.physicalModulation`
- Truth anchor: `D5/S3/Quantum/Analysis/ModulationMaximalDomain.physical_modulation_hasDerivAt_iff`
