# Real-mesh interpolation and polynomial specialization

## Abstract

Weighted pressure interpolation on increasing real meshes

**Theorem 1.1 (Uniform geometry for every natural r>=2 and k>=4).**

$$\forall r \in \mathbb{N},\; 2 \le r \Rightarrow \left(\forall k \in \mathbb{N},\; 4 \le k \Rightarrow \left(\operatorname{pow}\left(k + 1, r\right) \le \operatorname{pow}\left(2, r\right) \cdot \operatorname{pow}\left(k, r\right) \land \left(\operatorname{pow}\left(k + 1, r\right) - \operatorname{pow}\left(k, r\right) \le r \cdot \operatorname{pow}\left(2, r - 1\right) \cdot \frac{\operatorname{pow}\left(k, r\right)}{k} \land \operatorname{pow}\left(k + 1, r\right) \le \operatorname{pow}\left(\operatorname{pow}\left(k, r\right), 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.mesh_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N=k^r, H=2^r and G=r*2^(r-1), with the natural powers cast to the reals. The next mesh point is at most H*N, its distance from N is at most G*N/k, and it is at most N^2. The pow_step estimate applies Mathlib abs_pow_sub_pow_le to obtain (t+1)^(n+1)-t^(n+1)<=(n+1)*(t+1)^n for t>=0. mesh_bracket specializes the least-index construction to the polynomial mesh. power_atTop supplies divergence, and power_large supplies the positive base used to rewrite N/k as N^(1-1/r) in polynomial_gap.

mesh_power_balance converts r*(a+beta)<=r+1 into N^a*N^beta<=N*k for k>=1. price_gap bounds price(a)-price(b) by 2*(b-a)/(a^2*log(a)) when 1<a<=b and log(a)>=1. record_weight bounds P^a*log(P) by 4*L^a*log(L) for 0<=a<=1, P>1, L>=2 and P<=2*L. price_gap is used in real-mesh interpolation, and record_weight is used to transport the Robin lower bounds.

W_factor is the exact positive-base exponent identity. sample_exponent_lower preserves the same nonnegative lower-bound constant when the exponent decreases at a base greater than one. rescale_lower transports a fixed nonpositive lower bound through a nonnegative bounded weight ratio.

**Theorem 1.2 (An eventual pressure bound on a real mesh extends to the full real tail).**

$$\forall mesh \in \mathbb{N} \to \mathbb{R},\; \operatorname{StrictMono}\left(mesh\right) \Rightarrow \left(\left(\forall Y \in \mathbb{R},\; \exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow Y \le mesh\left(k\right)\right) \Rightarrow \left(\forall G \in \mathbb{R},\; \forall eta \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall C \in \mathbb{R},\; \forall A \in \mathbb{R},\; 0 \le G \Rightarrow \left(0 < eta \Rightarrow \left(0 \le alpha \Rightarrow \left(alpha \le 1 \Rightarrow \left(0 \le beta \Rightarrow \left(0 \le C \Rightarrow \left(0 \le A \Rightarrow \left(alpha + beta - eta \le 1 \Rightarrow \left(\left(\exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow mesh\left(k + 1\right) - mesh\left(k\right) \le G \cdot \operatorname{rpow}\left(mesh\left(k\right), 1 - eta\right)\right) \Rightarrow \left(\left(\forall X \in \mathbb{R},\; 2 \le X \Rightarrow \left|X - \operatorname{clock}\left(X\right)\right| \le C \cdot \operatorname{rpow}\left(X, beta\right)\right) \Rightarrow \left(\left(\exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow -A \le \operatorname{W}\left(alpha, mesh\left(k\right)\right) \cdot \operatorname{S}\left(mesh\left(k\right)\right)\right) \Rightarrow \left(\exists B \in \mathbb{R},\; 0 \le B \land \left(\exists T \in \mathbb{R},\; \forall X \in \mathbb{R},\; T \le X \Rightarrow -B \le \operatorname{W}\left(alpha, X\right) \cdot \operatorname{S}\left(X\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_mesh_samples_to_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write W(a,X)=X^a*log(X) and S(X)=EulerGamma+log(log(X))-1/log(X)-pressure(price(X)). The mesh is strictly increasing and tends to positive infinity. The gap and sample bounds each hold eventually in the natural index. The clock bound holds at every real X>=2. The exponent balance includes equality.

The least next mesh point above X gives a bracket n<=X<mesh(k+1), where n=mesh(k). On the chosen tail the gap bound gives X<=(1+G)*n<=n^2. The pressure integral and the derivative of log(log(X))-1/log(X) give |S(X)-S(n)|<=E*(price(n)-price(X)), with E=C*((1+G)*n)^beta. Combining price_gap with the gap bound leaves the power n^(alpha+beta-eta-1) after weighting at n. It is at most one by the exponent balance. The proof uses W(alpha,X)<=2*(1+G)*W(alpha,n) and rescale_lower to transport the resulting lower bound to X.

**Theorem 1.3 (From natural polynomial samples to the full real tail).**

$$\forall r \in \mathbb{N},\; 2 \le r \Rightarrow \left(\forall beta \in \mathbb{R},\; \forall sigma \in \mathbb{R},\; \forall C \in \mathbb{R},\; \forall A \in \mathbb{R},\; 0 \le C \Rightarrow \left(0 \le A \Rightarrow \left(\frac{1}{2} < sigma \Rightarrow \left(sigma < 1 \Rightarrow \left(0 \le beta \Rightarrow \left(beta - \frac{1}{r} < sigma \Rightarrow \left(\left(\forall X \in \mathbb{R},\; 2 \le X \Rightarrow \left|X - \operatorname{clock}\left(X\right)\right| \le C \cdot \operatorname{rpow}\left(X, beta\right)\right) \Rightarrow \left(\left(\exists K \in \mathbb{N},\; \forall k \in \mathbb{N},\; K \le k \Rightarrow -A \le \operatorname{W}\left(1 - sigma, \operatorname{pow}\left(k, r\right)\right) \cdot \operatorname{S}\left(\operatorname{pow}\left(k, r\right)\right)\right) \Rightarrow \left(\exists B \in \mathbb{R},\; 0 \le B \land \left(\exists T \in \mathbb{R},\; \forall X \in \mathbb{R},\; T \le X \Rightarrow -B \le \operatorname{W}\left(1 - sigma, X\right) \cdot \operatorname{S}\left(X\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_samples_to_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take mesh(k) to be the real cast of k^r, G=r*2^(r-1), eta=1/r and alpha=1-sigma in pressure_mesh_samples_to_all. Strict increase and divergence come from the natural powers. polynomial_gap supplies the eventual gap bound, and beta-1/r<sigma implies alpha+beta-eta<=1. The same W and S give the original polynomial sample bound and the same real-tail conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.mesh_geometry`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_mesh_samples_to_all`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PolynomialMeshBounds.pressure_samples_to_all`
- Dependency: [D5/S3/Arith/Robin/ActualRobinInterval](../ActualRobinInterval.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](../ActualTwoPriceDefect.md)
