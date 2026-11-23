# A Packing Bound for Finite Frequency Sums

## Abstract

The width of a frequency band forces a close pair of sums at fixed degree.

Let g on a finite index set J take values in the closed interval [a,b]. Let p be a natural number and M the multiset coefficient multichoose(|J|,p), and assume M≥2. For a nonnegative integer count vector m write F(m)=Σ m(j)g(j) and d(m)=Σ m(j). Define B=M when J has at least three indices and p≥2, and B=M−1 otherwise.

**Theorem 1.1 (Two distinct degree vectors have nearby frequencies).**

$$\exists m,n, m \ne n \land \left(\operatorname{d}\left(m\right) = p \land \left(\operatorname{d}\left(n\right) = p \land \left|\operatorname{F}\left(m\right)-\operatorname{F}\left(n\right)\right| \le \frac{p \cdot (b-a)}{B}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DegreeSpectrumPacking.exists_close_degree_vectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are M degree vectors by stars and bars. If any two give the same frequency, they have zero gap. Otherwise order the M values in [pa,pb]. The M−1 adjacent differences sum to at most p(b−a). For at least three indices and p≥2, the two end gaps are s−a₀ and b₀−t, where a₀,b₀ are the actual extremes and s,t the second smallest and second largest frequencies. The distinct degree-p sums (p−2)a₀+s+t and (p−1)a₀+b₀ differ by the difference of these gaps. If every gap exceeds a proposed lower threshold, one end gap exceeds twice it. The ordered span therefore pays for one additional gap.

For two endpoints a and b, the degree-p sums run through an arithmetic progression attaining the M−1 bound. At degree two the spectrum (0,1,3) attains the M bound. The existence of a close pair constrains possible uniform gap hypotheses. A weighted near-collision bound also needs control of the weights on all such pairs.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DegreeSpectrumPacking.exists_close_degree_vectors`
- Dependency: [D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow](FiniteTailMomentMissingWindow.md)
