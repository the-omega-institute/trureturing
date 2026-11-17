# The actual Robin source bridge

## Abstract

Own-clock fixed-support rounding for the original Robin margin.

S is any finite prime support with cardinal at least three. For every integer vector a_p>=1 define n=product_S p^(a_p.toNat); the nonnegative integer cast is proved to preserve every supported exponent. The exact support is n.primeFactors=S. EulerGamma, sigma(n)/n and the nonlinear original clock are retained.

**Theorem 1.1 (The actual product supplies the clock).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.support_integer_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.support_integer_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural exponent vector on a finite prime S, log(product_S p^a_p)=sum_S a_p log p. Nonzero factors justify Real.log_prod. This is consumed by the original-margin identity.

**Theorem 1.2 (The fixed-support objective is exactly robinLogMargin).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.phi_eq_robin_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.phi_eq_robin_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nat.factorization_prod and Prime.factorization_pow identify every actual valuation and the support containment. golden_resource_objective_sum_on at price zero and golden_resource_sigma_identity give the exact log(sigma(n)/n) sum. Real powers at natural exponents agree with the existing integer local Euler factors. Hence Phi(a)=robinLogMargin(n), with no free gamma and no modified divisor ratio.

**Theorem 1.3 (The original margin pays the own-clock rounding sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.original_margin_own_clock_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.original_margin_own_clock_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite prime S with cardinal>=3 and every supported integer vector a_p>=1, let L=log n, lambda=1/(L log L), C=1+lambda^-1, b_p=max(1,log C/log p-1), T=sum_S b_p log p, J_p=F_p(b_p)-F_p(a_p), and R_S the real infimum of the same Phi over x_p>=1 on S. The conclusion gives n.primeFactors=S, L=sum_S a_p log p, and robinLogMargin(n)-R_S=(Phi(b)-R_S)+sum_S J_p+[g(L)+lambda*(T-L)-g(T)], with nonnegative first term, each J_p, and the final tangent remainder. It gives 0<=sum_S d_p<=robinLogMargin(n)-R_S at this same own price.

The same conclusion includes every prime's exact active/inactive formulas. If p^2<C, J_p=D_Ber(C^-1||p^(-a_p-1))/(1-C^-1) and d_p is the minimum of the two scaled KL values at floor c_p,ceil c_p. If C<=p^2, including equality, b_p=1, d_p=0 and J_p=D_Ber(p^-2||p^(-a_p-1))/(1-p^-2)+(lambda-1/(p^2-1))*(a_p-1)*log p, with nonnegative scaled KL and excess-price coefficient. Integral critical exponents and simultaneous candidate ties are retained.

This is deterministic fixed-support rounding only. No explicit six-band coefficient, unique nonlinear real minimizer, Nicolas baseline sign, support reduction for all integers, strict positivity for n>5040, RH implication or full Robin/5040 theorem is asserted. Initial support at P>=13 automatically lies above 5040; smaller supports still need the original n>5040 restriction in downstream positivity arguments. The six-band bound with literal prime containment and explicit prime-count ranges is the next substantive stage. Neither an RH-dependent baseline nor a qualitative allocation asymptotic pays the unconditional remaining endpoint obligation. Reg registration and repository admission remain separate from these mathematical statements.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.original_margin_own_clock_gap`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.phi_eq_robin_margin`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockRobinGap.support_integer_log`
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../../GoldenResourceObjectiveFactorization.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport](OwnClockFixedSupport.md)
- Dependency: [D5/S3/Weil/GronwallLowerEnvelope](../../../Weil/GronwallLowerEnvelope.md)
