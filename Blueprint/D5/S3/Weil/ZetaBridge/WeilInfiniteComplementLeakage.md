# Weil Infinite Complement Leakage

## Abstract

A convergent infinite exterior Fourier tail has quantitatively little mass in the low-frequency quarter band, without an upper mode cutoff.

L is a positive real window length and N is a positive natural number. The sequences u,v : N -> C are square summable, with no finite upper support constraint. SquareMass(u) is sum_j |u_j|^2. The private Cauchy sum C(d,u)=sum_j u_j/(d+j+1) is absolutely convergent for d>0. The phase-adjusted orthonormal Fourier basis on [-L/2,L/2] is (-1)^n/sqrt(L)*exp(2*pi*i*n*x/L). u_j and v_j index modes N+j+1 and -(N+j+1).

**Definition 1.1 (An explicit infinite-tail Cauchy density).**

$$\operatorname{D}(L, N, u, v, s)=\operatorname{div}(L, {pi}^{2}) {\operatorname{sin}(pi s)}^{2} {\operatorname{norm}(\operatorname{C}(N+s, u)-\operatorname{C}(N-s, v))}^{2}$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.exteriorFourierDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula is evaluated on |s|<=N/4, away from every denominator zero. Physical frequency is t=2*pi*s/L. The identification with the Fourier transform of a general L2 exterior mode expansion is proved on paper in the existing source analysis; it has not been imported as an extra Lean theorem or axiom.

**Theorem 1.2 (Infinite tails cannot concentrate in the low-frequency quarter band).**

$$\operatorname{Positive}(N)\land \operatorname{Positive}(L)\land \operatorname{SquareSummable}(u)\land \operatorname{SquareSummable}(v)\Rightarrow \operatorname{IntervalIntegrableOnQuarterBand}(L, N, u, v)\land \operatorname{NormalizedQuarterBandIntegral}(L, N, u, v)\leq \operatorname{div}(4, 3 {pi}^{2}) \operatorname{SquareMass}(u)+\operatorname{SquareMass}(v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.infinite_complement_low_frequency_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive(x) means 0<x. SquareSummable means Summable of the squared complex norms. IntervalIntegrableOnQuarterBand means Lebesgue interval integrability of D between -N/4 and N/4. NormalizedQuarterBandIntegral is (1/L)*integral_{-N/4}^{N/4}D(s) ds. The proof first bounds the inverse-square partial sums by a telescoping reciprocal difference. It then proves absolute convergence, Cauchy-Schwarz for the infinite response, uniform series continuity, and the integral inequality. Thus neither a nonconvergent total sum nor a nonintegrable total integral is being assigned zero to make the conclusion vacuous. The all-form-domain arithmetic lower bound beta(a,N), the explicit prime-containing scale example, and the full operator Schur estimate remain paper results in this increment. This theorem makes no assumption about a spectral gap, ground-state parity, or zeros of Xi.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.exteriorFourierDensity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.infinite_complement_low_frequency_mass`
