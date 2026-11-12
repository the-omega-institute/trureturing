# The five-dimensional cutoff series in MathOverflow 511715

## Abstract

The exact Euclidean five-dimensional cutoff series and the failure of its uniform cutoff estimate.

The source is mathex, Bound of series, MathOverflow question 511715, revision 2, GUID A50CBAFD-9172-43CB-AD5D-4D59C3663AAC, https://mathoverflow.net/questions/511715/bound-of-series, licensed CC BY-SA 4.0. Its scalar field and vector norm are not specified. Here the vector norm is Euclidean, and both real and complex cutoffs are included. Constants may depend on the individually fixed cutoff. The question does not give a full cutoff quantifier prefix, scalar types or signs for C and delta, or a definition of R_+. The claim below uses finite C>=0, delta>0, and nonnegative time, including the explicitly requested zero endpoint. These disclosed conventions do not resolve the author's unspecified intent.

The complete published question and its correspondence with the conventional Euclidean real and complex readings are recorded in Problems/mathex-2026-mo511715-cutoff-bound.md. Under these readings, the result below negates the uniform cutoff estimate for the complete series. The obstruction uses one legal mask and the same fixed cutoff throughout.

Write Z for the lattice of five integer coordinates and E for Euclidean five-space. The map embed casts coordinates from Z into E. Set frequency(k)=norm(2*pi*embed(k)). The legal masks take values in [0,1], and a nonzero value at (k,l) implies (9/64)*norm(k)<=norm(l)<=(64/9)*norm(k). Both support boundaries are inclusive.

**Definition 1.1 (The original time integral).**

$$\forall q \in \mathbb{R},\; \forall L \in \mathbb{R},\; \forall A \in \mathbb{R},\; \forall B \in \mathbb{R},\; 0 \le q \Rightarrow \operatorname{timeIntegral}\left(q, L, A, B\right) = \int_{0}^{q} \operatorname{exp}\left(0 - L \cdot \left(q - t\right)\right) \cdot \int_{0}^{t} \int_{0}^{t} \operatorname{exp}\left(0 - A \cdot \left(q + t - 2 \cdot v\right) - B \cdot \left(q + t - 2 \cdot w\right)\right) dw dv dt$$

*Formalization.* `D5/S3/Fourier/MO511715Source.timeIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

The source definition integrates directly over the complete closed square with product Lebesgue measure. Its exponential is continuous and integrable on that compact set. Fubini's theorem and the zero measure of interval endpoints give the displayed iterated form for nonnegative time. No ordering between the inner variables is imposed.

**Definition 1.2 (The source kernel).**

$$\forall p \in \mathbb{Z}^{5} \to \mathbb{Z}^{5} \to \mathbb{R},\; \forall q \in \mathbb{R},\; \forall n \in \mathbb{Z}^{5},\; \forall a \in \mathbb{Z}^{5},\; \forall b \in \mathbb{Z}^{5},\; \operatorname{kernel}\left(p, q, n, a, b\right) = \operatorname{frequency}\left(n - a\right)^{2} \cdot \operatorname{p}\left(n - a, a\right) \cdot \operatorname{timeIntegral}\left(q, \operatorname{frequency}\left(n - a\right)^{4}, \operatorname{frequency}\left(a - b\right)^{4}, \operatorname{frequency}\left(b\right)^{4}\right)$$

*Formalization.* `D5/S3/Fourier/MO511715Source.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

All Fourier factors are retained: the prefactor is the squared frequency and each decay rate is the fourth power of its own frequency. The definition divides by no mode.

**Definition 1.3 (The two absolute-square cutoff factors).**

$$\forall F \in Type,\; [\operatorname{NormedAddCommGroup}\left(F\right)], \forall z \in \mathbb{R}^{5} \to F,\; \forall e \in \mathbb{R},\; \forall a \in \mathbb{Z}^{5},\; \forall b \in \mathbb{Z}^{5},\; \operatorname{cutoffWeight}\left(z, e, a, b\right) = \operatorname{norm}\left(\operatorname{z}\left(e \cdot \operatorname{embed}\left(a - b\right)\right)\right)^{2} \cdot \operatorname{norm}\left(\operatorname{z}\left(e \cdot \operatorname{embed}\left(b\right)\right)\right)^{2}$$

*Formalization.* `D5/S3/Fourier/MO511715Source.cutoffWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

Scalar norms mean real absolute value or complex modulus. The same cutoff and scale are used in both factors.

**Definition 1.4 (The complete ordered-pair lattice sum).**

$$\forall F \in Type,\; [\operatorname{NormedAddCommGroup}\left(F\right)], \forall z \in \mathbb{R}^{5} \to F,\; \forall p \in \mathbb{Z}^{5} \to \mathbb{Z}^{5} \to \mathbb{R},\; \forall e \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall n \in \mathbb{Z}^{5},\; \operatorname{phi}\left(z, p, e, q, n\right) = \sum_{(a,b) \in \operatorname{Product}\left(\mathbb{Z}^{5}, \mathbb{Z}^{5}\right)} \operatorname{kernel}\left(p, q, n, a, b\right) \cdot \operatorname{cutoffWeight}\left(z, e, a, b\right)$$

*Formalization.* `D5/S3/Fourier/MO511715Source.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

The sum ranges over all ordered pairs in Z times Z, including all zero modes. At a positive scale, compact support restricts both difference coordinates to bounded sets. The integer-to-Euclidean embedding is part of each cutoff argument.

**Definition 1.5 (The zero-output subtraction).**

$$\forall F \in Type,\; [\operatorname{NormedAddCommGroup}\left(F\right)], \forall z \in \mathbb{R}^{5} \to F,\; \forall p \in \mathbb{Z}^{5} \to \mathbb{Z}^{5} \to \mathbb{R},\; \forall e \in \mathbb{R},\; \forall r \in \mathbb{R},\; \forall u \in \mathbb{Z}^{5},\; \operatorname{delta}\left(z, p, e, r, u\right) = \operatorname{phi}\left(z, p, e, r, u\right) - \operatorname{phi}\left(z, p, e, r, 0\right)$$

*Formalization.* `D5/S3/Fourier/MO511715Source.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

The same mask and cutoff occur in the value at u and the value at zero.

**Definition 1.6 (The complete uniform estimate in both scalar readings).**

$$claim \Leftrightarrow \left(\left(\forall z \in \mathbb{R}^{5} \to \mathbb{R},\; \operatorname{SmoothCutoff}\left(z\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\exists d \in \mathbb{R},\; 0 < d \land \left(\forall p \in \mathbb{Z}^{5} \to \mathbb{Z}^{5} \to \mathbb{R},\; \operatorname{LegalMask}\left(p\right) \Rightarrow \left(\forall r \in \mathbb{R},\; 0 \le r \Rightarrow \left(\forall u \in \mathbb{Z}^{5},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left|\operatorname{delta}\left(z, p, b, r, u\right) - \operatorname{delta}\left(z, p, a, r, u\right)\right| \le C \cdot \left|b - a\right|^{d}\right)\right)\right)\right)\right)\right)\right) \land \left(\forall z \in \mathbb{R}^{5} \to \mathbb{C},\; \operatorname{SmoothCutoff}\left(z\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\exists d \in \mathbb{R},\; 0 < d \land \left(\forall p \in \mathbb{Z}^{5} \to \mathbb{Z}^{5} \to \mathbb{R},\; \operatorname{LegalMask}\left(p\right) \Rightarrow \left(\forall r \in \mathbb{R},\; 0 \le r \Rightarrow \left(\forall u \in \mathbb{Z}^{5},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left|\operatorname{delta}\left(z, p, b, r, u\right) - \operatorname{delta}\left(z, p, a, r, u\right)\right| \le C \cdot \left|b - a\right|^{d}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/MO511715Source.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

A smooth cutoff is compactly supported, infinitely differentiable over the reals, and equals one at zero. For each fixed cutoff, C is finite and nonnegative and the real exponent is positive. The estimate quantifies every legal mask, every nonnegative time, every lattice output, and both positive scales. Coincident scales, time zero and all positive scales remain included. No symmetry, regularity or partition identity is imposed on the mask, and no radiality, monotonicity or common support radius is imposed on the cutoff.

**Theorem 1.7 (A lower bound from a genuine time subregion).**

$$\forall L \in \mathbb{R},\; \forall A \in \mathbb{R},\; \forall B \in \mathbb{R},\; \forall h \in \mathbb{R},\; \left(0 \le L \land \left(0 \le A \land \left(0 \le B \land \left(0 < h \land \left(h \le \frac{1}{2} \land \left(L + 3 \cdot A + 3 \cdot B\right) \cdot h \le 1\right)\right)\right)\right)\right) \Rightarrow \operatorname{exp}\left(0 - 1\right) \cdot h^{3} \le \operatorname{timeIntegral}\left(1, L, A, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MO511715Source.time_integral_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

Restrict the outer variable to [1-h,1] and each inner variable to [alpha-h,alpha]. The assumption h<=1/2 puts this subregion inside the original square. Its iterated volume is h cubed. On this same subregion, 1-alpha<=h and 1+alpha-2*v<=3*h. Thus the total decay exponent is at most one. Continuity supplies integrability on every interval, and nonnegativity permits restriction of each integral.

**Theorem 1.8 (Finite support at every positive scale).**

$$\forall F \in Type,\; [\operatorname{NormedAddCommGroup}\left(F\right)], \forall z \in \mathbb{R}^{5} \to F,\; \forall e \in \mathbb{R},\; \left(\operatorname{HasCompactSupport}\left(z\right) \land 0 < e\right) \Rightarrow \operatorname{Finite}\left(\operatorname{support}\left((a,b) \mapsto \operatorname{cutoffWeight}\left(z, e, a, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MO511715Source.cutoff_finite_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

Compact support gives a radius R outside which the cutoff vanishes. A nonzero weight forces both Euclidean difference vectors to have norm less than R/e. Each integer coordinate is bounded by that norm, so the two vectors belong to finite coordinate boxes. The inverse map (a,b) to (a+b,b) gives a finite set of original ordered indices. Every source sum is therefore summable at positive scale, without a convergence assumption.

Let e be the first coordinate unit. The selected mask is one precisely when k+l=e and the two inclusive source support inequalities hold; it is zero otherwise. At the actual source arguments, k+l=n. Thus every output except e vanishes, and delta at e is exactly phi at e. This is one fixed mask for every scale and cutoff.

The box B(N) consists of all integer vectors with N<=a(i)<2*N in each of the five coordinates. It has exactly N to the fifth power elements. Its ordered pair block has N to the tenth power elements. Write D=2*pi, eta=1/(20000*D^4), kappa=D^2*exp(-1)*eta^3 and c=kappa/16. Both constants are strictly positive.

**Theorem 1.9 (The actual kernel on a lattice block).**

$$\forall N \in \mathbb{N},\; \forall a \in \mathbb{Z}^{5},\; \forall b \in \mathbb{Z}^{5},\; \left(1 \le N \land \left(a \in \operatorname{blockBox}\left(N\right) \land b \in \operatorname{blockBox}\left(N\right)\right)\right) \Rightarrow \frac{\operatorname{kernelConstant}\left(\right)}{N^{10}} \le \operatorname{kernel}\left(\operatorname{selectedMask}\left(\right), 1, \operatorname{firstUnit}\left(\right), a + b, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MO511715Source.kernel_block_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

For a,b in B(N), their norms are at most 5*N. The norm of a+b is between 4*N and 9*N, while the norm of e-a-b is between N and 10*N. The triangle inequalities also give both original support comparisons, so the selected mask equals one. Take h=eta/N^4 in the time-integral bound. The decay budget is at most (10^4+6*5^4)/20000=11/16. Multiplying by the actual frequency-squared prefactor gives kappa/N^10. No hypothesized kernel estimate is used.

**Theorem 1.10 (Simultaneous cutoff control across disjoint blocks).**

$$\forall F \in Type,\; [\operatorname{RCLike}\left(F\right)], \forall z \in \mathbb{R}^{5} \to F,\; \left(\operatorname{ContinuousAt}\left(z, 0\right) \land \left(\operatorname{z}\left(0\right) = 1 \land \operatorname{HasCompactSupport}\left(z\right)\right)\right) \Rightarrow \left(\exists r \in \mathbb{R},\; 0 < r \land \left(r \le 1 \land \left(\forall J \in \mathbb{N},\; \operatorname{blockConstant}\left(\right) \cdot \left(J + 1\right) \le \operatorname{phi}\left(z, \operatorname{selectedMask}\left(\right), \frac{r}{5 \cdot 2^{J}}, 1, \operatorname{firstUnit}\left(\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MO511715Source.phi_dyadic_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

Continuity and normalization give a radius 0<rho<=1 on whose closed ball the cutoff modulus is at least one half, for either scalar field. At scale rho/(5*2^J), both cutoff factors obey this bound simultaneously on every B(2^j) with j<=J. Their squared product is at least 1/16. The half-open dyadic boxes are pairwise disjoint, and the exact ordered-index bijection preserves their disjointness. Each block contributes at least c; nonnegative omitted terms give c*(J+1).

**Theorem 1.11 (Negation of the complete conventional source claim).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/MO511715Source.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* mathex (MathOverflow user 138491) (2026). *Bound of series*. URL: <https://mathoverflow.net/questions/511715/bound-of-series>.

*Commentary.*

The stronger obstruction holds for every individually fixed continuous-at-zero normalized compact cutoff over either the real or complex scalars, and every pair of finite real numbers C and delta, without sign restrictions. Keep that same cutoff and the same legal selected mask on both sides, with time one and output e. The reference scale is two; the comparison scale epsilon=rho/(5*2^J) satisfies 0<epsilon<=rho/5<=1/5. Thus both scales are strictly positive and distinct, and 1<=abs(2-epsilon)<=2. For every real delta, abs(2-epsilon)^delta<=H=max(1,2^delta): monotonicity in the base gives the bound when delta>=0, and a base at least one gives a bound of one when delta<=0. Consequently C*abs(2-epsilon)^delta<=max(C,0)*H. The fixed reference value M=phi(2,1,e) is finite. Choose J so that c*(J+1)>M+max(C,0)*H. The growth bound then makes the actual absolute delta difference strictly larger than the proposed right side. This includes zero and negative exponents and constants. Taking nonnegative C and a positive exponent refutes the conventional estimate for every such cutoff. A standard smooth real bump then negates the conjunction claim. Every smooth normalized compact cutoff in either scalar reading satisfies the stronger lemma's hypotheses. The source's unspecified norm and typing remain documentary omissions; this conventional reading certifies neither authorial intent nor an arbitrary-norm result, and assumes no additional mask structure.

## References

- Truth anchor: `D5/S3/Fourier/MO511715Source.claim`
- Truth anchor: `D5/S3/Fourier/MO511715Source.cutoffWeight`
- Truth anchor: `D5/S3/Fourier/MO511715Source.cutoff_finite_support`
- Truth anchor: `D5/S3/Fourier/MO511715Source.delta`
- Truth anchor: `D5/S3/Fourier/MO511715Source.kernel`
- Truth anchor: `D5/S3/Fourier/MO511715Source.kernel_block_lower`
- Truth anchor: `D5/S3/Fourier/MO511715Source.phi`
- Truth anchor: `D5/S3/Fourier/MO511715Source.phi_dyadic_growth`
- Truth anchor: `D5/S3/Fourier/MO511715Source.result`
- Truth anchor: `D5/S3/Fourier/MO511715Source.timeIntegral`
- Truth anchor: `D5/S3/Fourier/MO511715Source.time_integral_ge`
