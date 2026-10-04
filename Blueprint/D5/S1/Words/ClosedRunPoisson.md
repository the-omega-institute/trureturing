# Poisson Error for Closed Fair Words

## Abstract

Bound the probability that one closed fair Boolean word avoids k consecutive ones.

The probability law is uniform on all functions from Fin n to Bool, equivalently n independent fair bits. It is not conditioned on legality. Let G(n,k)=dbonacci(k,n+2), p=G(n,k)/2^n, and mu=(n-k+2)/2^(k+1). A forbidden block occupies k contiguous coordinates entirely within the word. There are N=n-k+1 possible starts. Position zero requires k ones; every later start also requires a preceding zero. Thus W counts run beginnings, with probabilities 2^(-k) at zero and 2^(-k-1) elsewhere, and mean mu.

**Theorem 1.1 (Uniform absolute error and two supplementary probability bounds).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \left(2 \le k \land k \le n\right) \Rightarrow \left(\Vert\frac{dbonacci\left(k, n + 2\right)}{2^{n}} - exp\left(-\frac{n - k + 2}{2^{k + 1}}\right)\Vert \le min\left(1, \frac{n - k + 2}{2^{k + 1}}\right) \cdot \left(k + 1\right) \cdot \frac{1}{2^{k}} \land \left(1 - \frac{dbonacci\left(k, n + 2\right)}{2^{n}} \le \frac{n - k + 2}{2^{k + 1}} \land \left(0 < \frac{n - k + 2}{2^{k + 1}} \Rightarrow \frac{dbonacci\left(k, n + 2\right)}{2^{n}} \le \frac{1}{\frac{n - k + 2}{2^{k + 1}}}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ClosedRunPoisson.closed_word_poisson_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard Arratia; Larry Goldstein; Louis Gordon (1990). *Poisson Approximation and the Chen-Stein Method*. DOI: [10.1214/ss/1177012015](https://doi.org/10.1214/ss/1177012015). URL: <https://doi.org/10.1214/ss/1177012015>.

*Commentary.*

For every n at least k at least two, the count ratio is exactly the probability W=0. The three bounds include n=k and k=2. The Poisson claim is an absolute error bound; it asserts no relative error or guaranteed error direction.

Each start depends on its k-bit block and optional predecessor. Its support is disjoint from the union of supports of all starts at distance greater than k, giving independence from the entire outside indicator tuple. Distinct nearby starts are mutually exclusive. The first marginal has double weight; counting it separately bounds every neighborhood mass by (k+1)2^(-k).

For F(z)=E[z^W], cancellation gives F'(z)=sum_i p_i E[z^V_i], where V_i counts outside starts. On [0,1], the defect F'-mu F lies between zero and the weighted neighborhood charge. Exponential integrating factors bound F(0) relative to exp(-mu), with coefficient (1-exp(-mu))/mu. A second derivative identity bounds E[W(W-1)] by mu^2, so Var(W) is at most mu. The pointwise indicator bound and Chebyshev's inequality give the two supplementary bounds under the same fair-word law. This is a closed-word adaptation of the classical long-run method.

## References

- Truth anchor: `D5/S1/Words/ClosedRunPoisson.closed_word_poisson_bounds`
- Dependency: [D5/S1/Words/ClosedRunStarts](ClosedRunStarts.md)
