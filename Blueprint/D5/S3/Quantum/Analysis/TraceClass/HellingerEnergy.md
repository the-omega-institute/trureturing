# Hellinger energy and the trace norm

## Abstract

A singular logarithmic energy bound for arbitrary noncommuting quantum states.

**Theorem 1.1 (The actual spectral diagonal).**

$$\operatorname{resolutiondiagonal}\left(FullSpectralResolutions\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.resolution_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

For every full actual resolution d of a positive trace-class contraction T and every vector v, the real series d(i)*norm(inner(v,d(i))) squared has the actual quadratic form Re inner(v,T v) as its sum. Square-root CFC eigenvector action and Parseval give genuine real summability. No trace normalization or finite entropy is required.

**Theorem 1.2 (Entropy in every full resolution).**

$$\operatorname{resolutionentropy}\left(FullSpectralResolutions\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.resolution_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

For every full actual resolution d of T, the nonnegative extended sum of -d(i) log(d(i)) equals spectralEntropy T. The generic spectral-energy identity and self energy prove the equality, including zero fibers and infinite entropy. No trace normalization is required.

**Theorem 1.3 (The full extended cross double series).**

$$\operatorname{resolutioncrossenergy}\left(FullSpectralResolutions\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.resolution_cross_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

For arbitrary full resolutions d of rho and e of sigma, the double sum (ofReal(d(i))*singularLog(e(j)))*ofReal(norm(inner(e(j),d(i))) squared) equals spectralEnergy sigma rho. The diagonal identity followed by nonnegative double summation proves it. This identity retains arbitrary index sets, full zero eigenspaces, zero times infinity and infinite cross energy, without normalization or finite-energy assumptions. It supplies both the Hellinger bound and the finite signed logarithmic formula.

**Theorem 1.4 (Entropy with a quantitative trace-norm reward).**

$$\forall H \in CompleteComplexHilbertSpace, rho \in \operatorname{Reference}\left(H\right), sigma \in \operatorname{Reference}\left(H\right),\; \left(\operatorname{PositiveTraceOne}\left(rho\right) \land \operatorname{PositiveTraceOne}\left(sigma\right)\right) \Rightarrow \operatorname{add}\left(\operatorname{spectralEntropy}\left(rho\right), \operatorname{ofReal}\left(\operatorname{divide}\left(\operatorname{square}\left(\operatorname{traceNorm}\left(\operatorname{subtract}\left(rho, sigma\right)\right)\right), 4\right)\right)\right) \le \operatorname{spectralEnergy}\left(sigma, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.spectralEntropy_add_traceNorm_sq_le_energy` (`✓ std3`). ∎

*Citation.* George Androulakis and Tiju Cherian John (2023). *Quantum f-divergences via Nussbaum-Szkoła Distributions and Applications to f-divergence Inequalities*. DOI: [10.48550/arXiv.2308.02929](https://doi.org/10.48550/arXiv.2308.02929). URL: <https://arxiv.org/html/2308.02929>.

*Commentary.*

Let H be any complete complex Hilbert space. The arguments rho and sigma are positive trace-class contractions with actual real trace one. The norm is the Banach trace norm on TraceClass H. Their native full spectral resolutions have arbitrary Set indices and retain every zero eigenvector. No separability, finite dimension, faithfulness, commutation or finite entropy is assumed.

For eigenvalues r,s in [0,1], the scalar inequality eta(r)+r+(sqrt(r)-sqrt(s)) squared <= r ell(s)+s follows from log(t)<=t-1 with t=sqrt(s)/sqrt(r). Here eta(0)=0 and ell(0)=infinity. If r=0 the equality is s=s; if r>0 and s=0 the right side is infinite. Zero times infinity remains zero.

For full native bases u and v, the transition weights c(i,j)=norm(inner(v(j),u(i))) squared have row and column sum one by unconditional Parseval. Square-root functional calculus acts on each eigenvector. Self-adjointness and Parseval identify the actual diagonal of rho at v(j) with the genuinely summable series sum r(i)c(i,j), and identify the square-root difference coordinates with (sqrt(r(i))-sqrt(s(j)))inner(v(j),u(i)).

The square roots are Hilbert-Schmidt because the original positive operators are trace class; their difference is Hilbert-Schmidt as well. Converting genuine real square sums to ENNReal and applying nonnegative double summation gives S(rho)+1+ofReal(HSdifferenceSquare)<=E_sigma(rho)+1. Only the finite trace-one addend is canceled. Infinite entropy, infinite cross energy and singular zero fibers are preserved.

The noncommuting identity rho-sigma=R(R-S)+(R-S)S, where R=sqrt(rho) and S=sqrt(sigma), combines with the Hilbert-Schmidt product trace-norm estimate and the triangle inequality. Both square roots have square sum one in the same full basis, so norm(rho-sigma)<=2 sqrt(HSdifferenceSquare). This yields the displayed reward. Dropping its nonnegative term gives the Gibbs inequality. The full weighted entropy theorem applies the stronger bound to both states relative to their actual mixture.

The spectral distribution viewpoint is the established Nussbaum-Szkola correspondence. Mathlib supplies functional calculus, Parseval and unconditional sums. The analytic trace-class and ideal estimates are the existing attributed Physlib suppliers; their provenance and licenses are unchanged. This bound does not prove entropy continuity, compactness of a state family, or existence of a common full-space Hamiltonian.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.resolution_cross_energy`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.resolution_diagonal`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.resolution_entropy`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/HellingerEnergy.spectralEntropy_add_traceNorm_sq_le_energy`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy](SpectralEnergy.md)
