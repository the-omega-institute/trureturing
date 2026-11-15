# Bounds consumed by the canonical-record criterion

## Abstract

Polynomial meshes and weighted lower-bound transport

**Theorem 1.1 (Uniform geometry for every natural r>=2 and k>=4).**

$$\forall r \in \mathbb{N},\; 2 \le r \Rightarrow \left(\forall k \in \mathbb{N},\; 4 \le k \Rightarrow \left(\operatorname{pow}\left(k + 1, r\right) \le \operatorname{pow}\left(2, r\right) \cdot \operatorname{pow}\left(k, r\right) \land \left(\operatorname{pow}\left(k + 1, r\right) - \operatorname{pow}\left(k, r\right) \le r \cdot \operatorname{pow}\left(2, r - 1\right) \cdot \frac{\operatorname{pow}\left(k, r\right)}{k} \land \operatorname{pow}\left(k + 1, r\right) \le \operatorname{pow}\left(\operatorname{pow}\left(k, r\right), 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.mesh_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N=k^r, H=2^r and G=r*2^(r-1), with the natural powers cast to the reals. The next mesh point is at most H*N, its distance from N is at most G*N/k, and it is at most N^2. The pow_step estimate applies Mathlib abs_pow_sub_pow_le to obtain (t+1)^(n+1)-t^(n+1)<=(n+1)*(t+1)^n for t>=0. mesh_bracket uses the least next mesh point to bracket every real X>=K^r. power_atTop supplies unboundedness, and power_large supplies the arithmetic logarithm domain.

mesh_power_balance converts r*(a+beta)<=r+1 into N^a*N^beta<=N*k for k>=1. price_gap bounds price(a)-price(b) by 2*(b-a)/(a^2*log(a)) when 1<a<=b and log(a)>=1. record_weight bounds P^a*log(P) by 4*L^a*log(L) for 0<=a<=1, P>1, L>=2 and P<=2*L. These bounds are consumed in the complete polynomial pressure interpolation and original-record transport; none asserts a zeta zero bound.

W_factor is the exact positive-base exponent identity. sample_exponent_lower preserves the same nonnegative lower-bound constant when the exponent decreases at a base greater than one. rescale_lower transports a fixed nonpositive lower bound through a nonnegative bounded weight ratio, treating the sign of the variable explicitly. These algebraic helpers have live consumers in PolynomialCanonicalRecordCriterion.result; they are proof organization rather than additional mathematical endpoints.

**Theorem 1.2 (From natural polynomial samples to the full real tail).**

$$\forall r \in \mathbb{N},\; 2 \le r \Rightarrow \left(\forall beta \in \mathbb{R},\; \forall sigma \in \mathbb{R},\; \forall C \in \mathbb{R},\; \forall A \in \mathbb{R},\; 0 \le C \Rightarrow \left(0 \le A \Rightarrow \left(\frac{1}{2} < sigma \Rightarrow \left(sigma < 1 \Rightarrow \left(0 \le beta \Rightarrow \left(beta - \frac{1}{r} < sigma \Rightarrow \left(\left(\forall X \in \mathbb{R},\; 2 \le X \Rightarrow \left|X - \operatorname{clock}\left(X\right)\right| \le C \cdot \operatorname{rpow}\left(X, beta\right)\right) \Rightarrow \left(\left(\exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow -A \le \operatorname{W}\left(1 - sigma, \operatorname{pow}\left(k, r\right)\right) \cdot \operatorname{S}\left(\operatorname{pow}\left(k, r\right)\right)\right) \Rightarrow \left(\exists B \in \mathbb{R},\; 0 \le B \land \left(\exists T \in \mathbb{R},\; \forall X \in \mathbb{R},\; T \le X \Rightarrow -B \le \operatorname{W}\left(1 - sigma, X\right) \cdot \operatorname{S}\left(X\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_samples_to_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here W(a,X)=X^a*log(X) and S(X)=EulerGamma+log(log(X))-1/log(X)-pressure(price(X)). For every natural r>=2, real beta,sigma,C,A with C,A>=0, 1/2<sigma<1, beta>=0 and beta-1/r<sigma, the displayed full-clock power bound and eventual natural sample lower bound imply one nonnegative uniform constant on the entire real tail. The compact-interval modulus follows from the complete pressure FTC and the derivative of log(log(X))-1/log(X). The polynomial mesh estimate pays the interpolation error, and sign-sensitive rescaling handles negative values of S. There is no beta<=1 assumption and no zero-strip premise. The complete closed-strip iff consumes this theorem internally.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.mesh_geometry`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_samples_to_all`
- Dependency: [D5/S3/Arith/Robin/ActualRobinInterval](../ActualRobinInterval.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](../ActualTwoPriceDefect.md)
