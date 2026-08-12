# Bhattacharyya Error Exponent and Sample Complexity

## Abstract

Bhattacharyya multiplicativity yields sharp and quadratic testing floors and an exponential sample-complexity inversion.

**Theorem 1.1 (Bhattacharyya affinity is multiplicative on i.i.d. powers).**

$$\rho(p^{n}, q^{n}) = \rho(p, q)^{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/BhattacharyyaExponent.bhattacharyya_iidPower_multiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This module answers the same two-law sample-complexity question as the earlier KL route, which used Kullback--Leibler divergence through Bretagnolle--Huber. The route here is genuinely different: Bhattacharyya overlap is multiplicative rather than additive, and every bound below quantifies over an arbitrary test.

The multiplicativity is what makes an exponent possible. The coefficient of n independent copies is exactly the n-th power of the single-copy coefficient. Combined with the single-copy floor, this gives error at least rho^(2n) / 2, so error can decay at most exponentially in the number of observations, at rate 2 log(1/rho). No test beats that rate, which is what gives a Chernoff-style exponent its meaning. The n-fold statement needs only that each product p i * q i is nonnegative, weaker than requiring p and q to be nonnegative separately; the induction genuinely propagates this weak form.

Both floors are kept, and the sharp one is strictly better everywhere. Composing the frozen Le Cam floor with the frozen total-variation/Bhattacharyya inequality gives 1 - sqrt(1 - rho^2); relaxing it gives the more quotable rho^2 / 2. Numerically, the sharp and quadratic floors are 0.046061 and 0.045000 at rho=0.3, 0.564110 and 0.405000 at rho=0.9, and 0.858933 and 0.490050 at rho=0.99. The sharp form is primary because it retains this tighter bound; the quadratic form remains exported because it is simpler to quote and compose.

The primary sample-complexity statement is the side-condition-free product form rho^(2n) <= 2*eps. The solved form divides by 2*log rho. Since log rho is negative for rho<1, that division reverses the inequality; the proof uses the negative-divisor lemma explicitly, and the theorem carries 0<rho<1 for exactly this reason. This is the one place where a plausible-looking statement could typecheck while being false. When rho=1 the two laws are identical and no finite number of observations suffices. For rho=0.9 and eps=0.01 the bound is n>=18.5649, hence at least 19 observations; for rho=0.99 it is n>=194.6215, hence at least 195. If 2*eps>=1, the product form reads rho^(2n)<=1 and is vacuous, correctly reflecting that such an error allowance needs no data. The cost blows up as rho approaches one and grows only logarithmically as the target error shrinks, so both informative and vacuous regimes matter.

**Theorem 1.2 (Sharp Bhattacharyya floor for every two-point test).**

$$1 - \sqrt {1 - \rho^{2}} \le e$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/BhattacharyyaExponent.testing_error_bhattacharyya_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharp floor is the direct composition of the frozen Le Cam two-point sum bound and the frozen total-variation/Bhattacharyya comparison. It applies to every acceptance event under normalized nonnegative laws, with no restriction to a selected test.

**Theorem 1.3 (Quadratic Bhattacharyya floor for every two-point test).**

$$\frac{\rho^{2}}{2} \le e$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/BhattacharyyaExponent.testing_error_bhattacharyya_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The elementary rho^2/2 floor is derived from the sharp form by the square-root inequality. It is weaker everywhere, but its compact expression is useful for direct exponent and sample-complexity calculations.

**Theorem 1.4 (Every i.i.d. test has a Bhattacharyya exponent floor).**

$$\frac{\rho^{2n}}{2} \le e$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/BhattacharyyaExponent.iid_testing_error_bhattacharyya` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the quadratic single-copy floor to the n-fold laws and then using exact affinity multiplicativity gives the universal lower bound rho^(2n)/2 for every test on independent observations.

**Theorem 1.5 (Side-condition-free Bhattacharyya sample-complexity product form).**

$$\rho^{2n} \le 2 \varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/BhattacharyyaExponent.bhattacharyya_sample_complexity_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an arbitrary n-observation test has total error at most eps, the exponent floor immediately yields rho^(2n) <= 2*eps. This is the primary form because it needs no side condition on rho or eps.

**Theorem 1.6 (Logarithmic Bhattacharyya sample-complexity inversion).**

$$\frac{\log (2\varepsilon)}{2 \log \rho} \le n$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/BhattacharyyaExponent.bhattacharyya_sample_complexity_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under 0<rho<1, positive eps, and 2*eps<=1, the product inequality can be solved for n. The negative logarithm reverses the division inequality, so the displayed logarithmic threshold is an explicit lower bound rather than an upper bound.

## References

- Truth anchor: `D5/S3/Estimation/BhattacharyyaExponent.bhattacharyya_iidPower_multiplicative`
- Truth anchor: `D5/S3/Estimation/BhattacharyyaExponent.bhattacharyya_sample_complexity_log`
- Truth anchor: `D5/S3/Estimation/BhattacharyyaExponent.bhattacharyya_sample_complexity_product`
- Truth anchor: `D5/S3/Estimation/BhattacharyyaExponent.iid_testing_error_bhattacharyya`
- Truth anchor: `D5/S3/Estimation/BhattacharyyaExponent.testing_error_bhattacharyya_quadratic`
- Truth anchor: `D5/S3/Estimation/BhattacharyyaExponent.testing_error_bhattacharyya_sharp`
- Dependency: [D5/S3/DivergenceSupport/PowerAdditivity](../DivergenceSupport/PowerAdditivity.md)
- Dependency: [D5/S3/Estimation/LeCam](LeCam.md)
- Dependency: [D5/S3/RenyiDivergence/PowerAdditivity](../RenyiDivergence/PowerAdditivity.md)
- Dependency: [D5/S3/TotalVariation/BhattacharyyaProduct](../TotalVariation/BhattacharyyaProduct.md)
