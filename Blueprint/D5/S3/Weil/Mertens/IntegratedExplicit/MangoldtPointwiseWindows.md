# One-sided bounds on a whole interval

## Abstract

Pointwise windows for the complete Mangoldt remainder

Write U(x) for x times the sum of Λ(n)/n over 1 ≤ n ≤ x, minus ψ(x) and x log x, plus (1+γ)x. Here Λ is the von Mangoldt function, ψ its summatory function and γ Euler’s constant. Fix b > 1. A window begins at Y ≥ 2 and contains every real x between Y and Yᵇ, including both endpoints.

**Theorem 1.1 (Arbitrarily small positive power losses).**

$$\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(RiemannHypothesis \Leftrightarrow \left(\forall k \in \mathbb{R},\; 0 < k \Rightarrow \left(\forall R \in \mathbb{R},\; \exists Y \in \mathbb{R},\; \operatorname{max}\left(R, 2\right) \le Y \land \left(\forall x \in \mathbb{R},\; \left(Y \le x \land x \le Y^{b}\right) \Rightarrow \operatorname{U}\left(x\right) \le x^{\frac{1}{2}+k}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows.rh_iff_pointwise_power_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH the normalized primitive U(x)/√x is eventually bounded in absolute value. For each k > 0, xᵏ eventually absorbs the fixed coefficient. The starting point may depend on k and the prescribed lower bound R.

For the converse let q be the integral of (θ(t)−t)/t² from x to infinity and Q the corresponding integral with ψ. The exact identity U(x)/x = −Q(x) and the limit √x(Q(x)−q(x)) → 2 bound the integral of max(−q(x),0)/√x on [Y,Yᵇ] by 4 Yᵇᵏ (b−1) log Y. Given any η > 0, choose k = η/(2b). The remaining factor 4(b−1) log Y is at most Y to the power η/2 at all sufficiently large Y. The prime-only window criterion now gives RH.

**Theorem 1.2 (A fixed coefficient at the square-root scale).**

$$\forall C \in \mathbb{R},\; \forall b \in \mathbb{R},\; firstLiMass < C \Rightarrow \left(1 < b \Rightarrow \left(RiemannHypothesis \Leftrightarrow \left(\forall R \in \mathbb{R},\; \exists Y \in \mathbb{R},\; \operatorname{max}\left(R, 2\right) \le Y \land \left(\forall x \in \mathbb{R},\; \left(Y \le x \land x \le Y^{b}\right) \Rightarrow \operatorname{U}\left(x\right) \le C\sqrt{x}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows.rh_iff_pointwise_sqrt_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first Li mass equals 2+γ−2 log(2√π). Under RH the full-axis envelope eventually bounds |U(x)|/√x by any larger C. Conversely, on a sufficiently late window C ≤ xᵏ for every x in that window, for each fixed k > 0. The first criterion gives RH. The proved inequality firstLiMass < 1/3 allows the explicit choice C = 1/3.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows.rh_iff_pointwise_power_windows`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows.rh_iff_pointwise_sqrt_windows`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth](PrimeWindowPoleGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/ZeroAbscissaPower](../ZeroAbscissaPower.md)
