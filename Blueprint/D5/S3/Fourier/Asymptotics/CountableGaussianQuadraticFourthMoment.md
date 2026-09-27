# Countable Gaussian Quadratic Fourth Moment

## Abstract

Square-summable centered Gaussian quadratic series converge in L4 with exact second and fourth moments.

**Theorem 1.1 (Actual infinite sums and their moments).**

$$\forall Omega \in Type, Sigma \in \operatorname{MeasurableSpace}\left(Omega\right), P \in \operatorname{Measure}\left(Omega, Sigma\right), G \in {\mathbb{N}\to {Omega\to \mathbb{R}}}, a \in {\mathbb{N}\to \mathbb{R}},\; \left(\left(\left(\operatorname{IsProbabilityMeasure}\left(P\right) \land \left(\forall j \in \mathbb{N},\; \operatorname{HasLaw}\left(G(j), \operatorname{gaussianReal}\left(0, 1\right), P\right)\right)\right) \land \operatorname{iIndepFun}\left(G, P\right)\right) \land \operatorname{Summable}\left((j:\mathbb{N}\mapsto a(j)^{2})\right)\right) \Rightarrow \left(\exists hm \in \left(\forall j \in \mathbb{N},\; \operatorname{MemLp}\left((omega:Omega\mapsto a(j) \cdot (G(j)(omega)^{2}-1)), 4, P\right)\right), X \in \operatorname{Lp}\left(\mathbb{R}, 4, P\right),\; \left(\left(\left(\left(\left(\operatorname{HasSum}\left((j:\mathbb{N}\mapsto \operatorname{toLp}\left(hm(j), (omega:Omega\mapsto a(j) \cdot (G(j)(omega)^{2}-1))\right)), X\right) \land \operatorname{MemLp}\left(X, 2, P\right)\right) \land \operatorname{Tendsto}\left((s:\operatorname{Finset}\left(\mathbb{N}\right)\mapsto \operatorname{eLpNorm}\left({(omega:Omega\mapsto \operatorname{finsetSum}\left(s, (j:\mathbb{N}\mapsto (omega:Omega\mapsto a(j) \cdot (G(j)(omega)^{2}-1))(omega))\right))-X}, 2, P\right)), atTop, \operatorname{nhds}\left(0\right)\right)\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{1})\right) = 0\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{2})\right) = 2 \cdot \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(j)^{2})\right)\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{4})\right) = 12 \cdot \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(j)^{2})\right)^{2}+48 \cdot \operatorname{tsum}\left((j:\mathbb{N}\mapsto a(j)^{4})\right)\right) \land \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{4})\right) \le 15 \cdot \operatorname{Integral}\left(P, (omega:Omega\mapsto X(omega)^{2})\right)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Nualart and Giovanni Peccati (2005). *Central limit theorems for sequences of multiple stochastic integrals*. DOI: [10.1214/009117904000000621](https://doi.org/10.1214/009117904000000621). URL: <https://arxiv.org/pdf/math/0503598v1>.

*Commentary.*

Let (Omega, Sigma, P) be any probability space. The countable family G(j) consists of independent real random variables with standard Gaussian law. Let a(j) be real coefficients whose squares are summable. Coefficients may be zero or negative, and their support may be infinite.

Write F(j)(omega)=a(j)(G(j)(omega)^2-1), T(s)(omega)=sum over j in the finite set s of F(j)(omega), and S=sum over j of a(j)^2. The theorem supplies proofs hm(j) that each actual term belongs to L4(P), and an element X of L4(P) to which their finite-subset sums converge in norm. The notation toLp(hm(j),F(j)) denotes the equivalence class of the actual function, modulo almost-everywhere equality. All integrals below use the measurable representative of X.

The representative X also belongs to L2(P), and eLpNorm(T(s)-X,2,P) tends to zero as s increases through all finite subsets. Its mean is zero, its second moment is 2S, and its fourth moment is 12S^2+48 sum over j of a(j)^4. In particular its fourth moment is at most fifteen times the square of its second moment. No higher integrability or series convergence is assumed.

For each finite subset, independence and the standard Gaussian even moments give the two exact moment identities. The fourth-power coefficient sum is at most the square of the square-sum, so every finite tail has fourth moment at most sixty times its coefficient square-sum squared. Completeness of L4 constructs the sum. Norm continuity passes the fourth moment to the limit, and exponent comparison gives the L2 and mean conclusions.

This is a coefficient-series moment calculation using classical Gaussian facts. The cited fixed-chaos literature provides related fourth-moment context; no claim of mathematical novelty is made. Identifying a prescribed spectral series with X requires equality of its L2 limit. This result alone asserts neither process tightness nor a stable limit.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.result`
