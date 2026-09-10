# Even Fourier Observation Tail

## Abstract

The full even Fourier tail admits an absolutely convergent complex-frequency response with cubic squared cutoff decay. The estimate controls the observable needed by the Weil-to-Xi route.

The actual window is [-L/2,L/2]. For n>0 use the existing phase-adjusted cosine basis (-1)^n*sqrt(2/L)*cos(2*pi*n*x/L), zero extended outside that interval, with Fourier kernel exp(i*z*x). The coefficient sequence v_j refers to n=N+j+1. The Fourier identification is a paper bridge in the existing RH source analysis.

**Definition 1.1 (The complete exterior response).**

$$\operatorname{evenExteriorResponse}(L, N, v, z)=\operatorname{CanonicalCosineTail}(L, N, v, z)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail.evenExteriorResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write w=z*L/(2*pi) and n_j=N+j+1. The response is [-L*sqrt(2*L)/(2*pi^2)]*z*sin(L*z/2) *sum_j v_j/(n_j^2-w^2). This is an infinite coefficient series, not an upper-truncated matrix. The theorem uses only L>0, N>0 and L*norm(z)<=pi*N, which exclude every denominator zero. No identity at a totalized removable pole is claimed.

**Theorem 1.2 (Absolute convergence and cubic squared tail bound).**

$$\operatorname{And}(\operatorname{Positive}(L), \operatorname{Positive}(N), \operatorname{SquareSummable}(v), \operatorname{LessEqual}(\operatorname{mul}(L, \operatorname{norm}(z)), \operatorname{mul}(pi, N)))\Rightarrow \operatorname{And}(\operatorname{AbsolutelySummable}(\operatorname{CauchyTerms}(L, N, v, z)), \operatorname{LessEqual}(\operatorname{normSq}(\operatorname{evenExteriorResponse}(L, N, v, z)), \operatorname{mul}(\operatorname{div}(\operatorname{mul}(8, \operatorname{cube}(L)), \operatorname{mul}(27, \operatorname{fourthPower}(pi), \operatorname{cube}(N))), \operatorname{normSq}(\operatorname{mul}(z, \operatorname{sin}(\operatorname{mul}(\operatorname{div}(L, 2), z)))), \operatorname{sumNormSq}(v))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail.even_exterior_fourier_observation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm restriction gives norm(n_j^2-w^2)>=3*n_j^2/4. A positive telescoping identity proves sum_{n>N} n^(-4)<=1/(3*N^3), including convergence. Young's inequality gives absolute summability of the coefficient products. Finite Cauchy-Schwarz followed by the sum limit gives the full infinite-series estimate. The physical Fourier factor is retained exactly.

For norm(z)<=R and abs(Im(z))<=b the paper consequence is norm(response)<=sqrt(8/(27*pi^4))*L^(3/2)*R*exp(b*L/2) *N^(-3/2)*norm(v). This applies to an arbitrary even L2 tail after the same-source Fourier/Parseval identification. If its arithmetic energy dominates beta*norm(v)^2, the squared observation budget is divided by beta.

The existing source analysis applies this estimate to the explicit, suitably normalized prolate model of Connes-Consani-Moscovici. It constructs an evenized, finite dyadic candidate family with the same Xi limit. That model-limit proof, the factor-four Mellin normalization calculation, and the observable Schur energy certificate are paper results. None is silently asserted by this Lean theorem. The fixed 129-entry numerical candidate has not been identified with that new family. No unbounded-scale ground approximation or RH conclusion is claimed. Lean and Scribe compilation were not run in this session.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail.evenExteriorResponse`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail.even_exterior_fourier_observation_bound`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage](WeilInfiniteComplementLeakage.md)
