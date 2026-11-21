# Effective prime counts in a varying residue class

## Abstract

Dyadic prime counts from two relative Chebotarev estimates

Write P(m,a;l,u) for the number of primes congruent to a modulo m in (l,u]. Let Li(t) be the integral of 1/log u from 2 to t, and set F(t) = Li(t) − θ Li(tᵝ). For a relative tolerance ε define M(ε,Y) = max(0, Y/log(2Y) − 24εY/log Y).

Write S(θ,β,Q,s) for the following conditions. The sign θ belongs to {−1,0,1}. When θ ≠ 0 the zero parameter satisfies ½ ≤ β ≤ 1. When θ = 1 it also satisfies s/(Q² log Q) ≤ 1 − β. The choice of β has no effect for θ = 0.

**Theorem 1.1 (Two endpoint estimates give a lower bound for the interval).**

$$\begin{aligned}&\forall m,a\in \mathbb{N},\,\forall \theta\in \mathbb{Z},\,\forall \beta,Y,Q,s,e,\varepsilon\in \mathbb{R},\,\\&Y\ge 16\land Q>1\land s>0\land \operatorname{S}\left(\theta, \beta, Q, s\right)\\&\land (\theta=1\implies Q\le Y)\\&\land (\forall t\in \{Y,2Y\},\,\lvert\varphi(m)(\operatorname{P}\left(m, a, 0, t\right)+e)-\operatorname{F}\left(t\right)\rvert\le \varepsilon \operatorname{F}\left(t\right))\\&\implies \frac{\operatorname{min}\left(1, s\right)}{2Q^{2}}\operatorname{M}\left(\varepsilon, Y\right)\le \varphi(m)\operatorname{P}\left(m, a, Y, 2Y\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DyadicPrimeClassCount.dyadic_class_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For θ = 1 set W = 1 − Y^(β−1), and otherwise set W = 1. The derivative (1 − θ t^(β−1))/log t gives an increment of at least WY/log(2Y). Integration also gives F(Y) + F(2Y) ≤ 24 WY/log Y. Subtracting the endpoint estimates cancels the common offset e. Nonnegativity of the count allows truncation at zero. The exceptional-zero distance gives W ≥ min(1,s)/(2Q²).

Write E(m,a,B,A,c,s,Y) for the relative estimate at this pair of endpoints. There exist 1 < Q ≤ m, θ, β and a common real offset e satisfying S(θ,β,Q,s). For each t in {Y,2Y} with t ≥ Qᴮ, the absolute difference between φ(m)(P(m,a;0,t) + e) and F(t) is at most A(exp(−c log t/log Q) + exp(−√(c log t))) F(t).

**Theorem 1.2 (One pair of thresholds works for every class with endpoint estimates).**

$$\begin{aligned}&\forall B,A,c,s,\varepsilon\in \mathbb{R},\,A>0\land c>0\land s>0\land \varepsilon>0\\&\implies \exists K,D_{0}\in \mathbb{R},\,K\ge 1\land D_{0}>0\land [\forall m,a\in \mathbb{N},\,\forall D\in \mathbb{R},\,\\&D\ge \operatorname{max}\left(D_{0}, 2m^{K}\right)\land \operatorname{E}\left(m, a, B, A, c, s, D/2\right)\\&\implies \frac{\operatorname{min}\left(1, s\right)}{2m^{2}}\operatorname{M}\left(\varepsilon, D/2\right)\le \varphi(m)\operatorname{P}\left(m, a, D/2, D\right)]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DyadicPrimeClassCount.uniform_dyadic_class_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take u = 2A/ε, K = max(1,B,u/c), and D₀ = 2 max(16,exp(u²/c)). At both D/2 and D, each exponential multiplied by A is at most ε/2. Apply the endpoint theorem with Q ≤ m.

For ε = 1/100 and Y = D/2 ≥ 16, use log(2Y) ≤ 2 log Y. Then M(ε,Y) ≥ (13/50)Y/log Y. Since φ(m) ≤ m, the count is at least (13/100) min(1,s) Y/(m³ log Y).

Thorner and Zaman, A unified and improved Chebotarev density theorem, Algebra & Number Theory 13 (2019), DOI 10.2140/ant.2019.13.1039, Theorem 1.4 (p. 1042) gives the relative asymptotic in writing, and Theorem 3.3 (p. 1052) gives the exceptional-zero distance. Take L = ℚ(ζₘ), H = Gal(L/ℚ) and fixed field ℚ. The character conductors divide m. For p coprime to m, Frobenius raises roots of unity to the pth power. For a reduced class and Y above m, the two prefixes may differ from the field counts by one common offset. The published estimate at these two heights supplies E in the Lean theorem.

## References

- Truth anchor: `D5/S3/CharacterSums/DyadicPrimeClassCount.dyadic_class_count`
- Truth anchor: `D5/S3/CharacterSums/DyadicPrimeClassCount.uniform_dyadic_class_count`
