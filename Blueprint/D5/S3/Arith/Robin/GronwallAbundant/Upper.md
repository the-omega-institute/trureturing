# Upper

## Abstract

Prime-deletion constraints, missing-prime mass and finite-code entropy for proper GA1 integers.

For a proper GA1 integer put T=log(N). Deleting any prime leaves at least four. The exact normalized divisor-sum ratio gives S*(log(log(N))-log(log(N/p)))<=log(log(N)), where S=1+p+...+p^v. The logarithmic gap is at least log(p)/T. CNS Theorem 9 gives p^r<=r*T for every occupied positive layer r; in particular every prime factor is at most T and every repeated prime is at most sqrt(2*T).

If P is the largest prime factor, W is the logarithmic mass of missing primes below P, and E is the mass beyond first prime copies, then T=theta(P)-W+E. Thus W<=psi(P)-P+E. For log(N)<=X, E<=72*X^(3/4). Splitting P at sqrt(X) makes the quantitative prime number theorem uniform over every smaller prefix. The fixed-power repetition term is absorbed into the same exponential power-logarithm allowance.

The integer is recovered from P, all exponents below floor(sqrt(2*X))+1, and the omitted large primes. A coarse exponent range through ceil(2*X) suffices. Each omitted large prime has logarithmic mass at least log(X)/2, so at most ceil(2*B/log(X))+1 are omitted when W<=B. Unique prime factorization makes this code injective. Weighted binomial sums bound its missing-set cost by K*(1+log(M/K)).

The rounded finite coordinates cost O(sqrt(X)*log(X)); the entropy and this cost are bounded by D*(X/log(X))*exp(-a*(log(X))^(1/10)) with positive a. If c0 is the MediumPNT constant, the uniform budget uses c=c0*2^(-1/10) and the terminal estimate uses a=c/2=c0*2^(-1/10)/2. Substituting X=log(x) gives the displayed bound for the original counting function. The constants and starting point are existential. No lower count estimate or conditional sharper upper scale is asserted.

This is one strict improvement answering the request in section 8 of Caveney, Nicolas and Sondow. The proved mechanism combines the same-integer prime endpoint barrier with missing-prime mass controlled by psi(y)-y. A lower counting bound depends on sign oscillations of theta(y)-y; that bridge remains unresolved. Under RH, a candidate scale for log(1+Q1(x)) is sqrt(log(x))*(log(log(x)))^O(1); no such conditional improvement is proved here.

**Theorem 1.1 (The actual counting function is bounded by the logarithmic cost of its injective code.).**

Lean statement: `D5/S3/Arith/Robin/GronwallAbundant/Upper.ga1_log_count_le_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Upper.ga1_log_count_le_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual counting function is bounded by the logarithmic cost of its injective code.

**Theorem 1.2 (The proper GA1 counting function has an exponential power-logarithm saving.).**

$$\exists a: \mathbb{R}, 0 < a \land \exists C: \mathbb{R}, 0 < C \land \exists r: \mathbb{R}, \forall x: \mathbb{R}, r \le x \Rightarrow \operatorname{log}\left(1 + \left(Q_{1}\right)\left(x\right)\right) \le C \cdot \frac{\operatorname{log}\left(x\right)}{\operatorname{log}\left(\operatorname{log}\left(x\right)\right)} \cdot \operatorname{exp}\left(-a \cdot \operatorname{log}\left(\operatorname{log}\left(x\right)\right)^{\frac{1}{10}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GronwallAbundant/Upper.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proper GA1 counting function has an exponential power-logarithm saving.

## References

- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Upper.ga1_log_count_le_cost`
- Truth anchor: `D5/S3/Arith/Robin/GronwallAbundant/Upper.result`
- Dependency: [D5/S3/Arith/Robin/GronwallAbundant/Asymptotic](Asymptotic.md)
