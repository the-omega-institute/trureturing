# Real exponential growth

## Abstract

Logarithmic growth and exponential norm bounds convert into one another; quadratic factors are absorbed by every positive real power in the exponent.

**Theorem 1.1 (Logarithm of one plus an exponential).**

$$\operatorname{log}\left(1 + \operatorname{exp}\left(x\right) \right) \le x + \operatorname{log}\left(2\right)   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_one_add_exp_le_add_log_two` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For every nonnegative real x, the displayed bound holds. The proof bounds one plus exp(x) by twice exp(x), then uses monotonicity of the real logarithm.

**Theorem 1.2 (Transport an exponential bound).**

$$\operatorname{log}\left(1 + y \right) \le x + \operatorname{log}\left(2\right)   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_one_add_le_add_log_two_of_le_exp` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For real x and y, assume both are nonnegative and y is at most exp(x). Monotonicity transports the preceding estimate to one plus y.

**Theorem 1.3 (Recover an exponential bound).**

$$y \le \operatorname{exp}\left(x\right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.le_exp_of_log_one_add_le` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For arbitrary real x and nonnegative real y, a bound log(1+y) at most x implies the displayed inequality. No nonnegativity assumption on x is imposed.

**Theorem 1.4 (An exponential dominates its argument).**

$$x \le \operatorname{exp}\left(x\right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.le_exp_self` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

Every real x is at most exp(x). This follows from the standard tangent-line inequality one plus x at most exp(x), including negative x.

**Theorem 1.5 (A logarithmic norm comparison).**

$$\operatorname{log}\left(\operatorname{norm}\left(w\right)\right) \le \operatorname{log}\left(1 + \operatorname{norm}\left(w\right) \right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_norm_le_log_one_add_norm` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For every element w of an arbitrary seminormed additive commutative group, the displayed inequality holds. Zero norm is treated using the total real logarithm.

**Theorem 1.6 (Nonnegative radius ratio logarithm).**

$$0 \le \operatorname{log}\left({r} \cdot {{\operatorname{norm}\left(z\right)} ^ {- 1 } } \right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_nonneg_mul_inv_norm_of_norm_le` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

In any normed additive commutative group, assume the norm of z is at most the real radius r. The logarithm of r times the inverse norm is nonnegative. The case z equals zero is included, with total inversion and logarithm.

**Theorem 1.7 (A doubled radius ratio).**

$$\operatorname{log}\left(2\right) \le \operatorname{log}\left({{2} \cdot {R} } \cdot {{\operatorname{norm}\left(z\right)} ^ {- 1 } } \right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_two_le_log_two_mul_mul_inv_norm_of_norm_le` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For nonzero z in any normed additive commutative group, if its norm is at most the real radius R, the displayed logarithm is at least log(2).

**Theorem 1.8 (Increase the growth exponent).**

$$\forall x , \operatorname{norm}\left(\operatorname{f}\left(x\right)\right) \le \operatorname{exp}\left({C} \cdot {{\operatorname{r}\left(x\right)} ^ {tau} } \right)   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.norm_le_exp_mul_rpow_of_exponent_le` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

Let f map any index type into a seminormed additive commutative group, and let r be a real radius function with r(x) at least one for every x. For nonnegative C and real rho at most tau, a pointwise norm bound exp(C r(x)^rho) implies the displayed bound at every x.

**Theorem 1.9 (From logarithmic to exponential growth).**

$$\forall x , \operatorname{norm}\left(\operatorname{f}\left(x\right)\right) \le \operatorname{exp}\left({C} \cdot {{\operatorname{r}\left(x\right)} ^ {tau} } \right)   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.norm_le_exp_mul_rpow_of_log_growth` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

With the same arbitrary index and seminormed codomain, assume C is nonnegative, all radii are at least one, and rho is at most tau. A pointwise bound log(1+norm(f(x))) at most C r(x)^rho implies the displayed norm bound.

**Theorem 1.10 (From exponential to logarithmic growth).**

$$\exists Cprime > 0 , \forall x , \operatorname{log}\left(1 + \operatorname{norm}\left(\operatorname{f}\left(x\right)\right) \right) \le {Cprime} \cdot {{\operatorname{r}\left(x\right)} ^ {tau} }     $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_growth_of_norm_le_exp_mul_rpow` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For an arbitrary index type and seminormed codomain, assume C is positive, tau is nonnegative, every radius is at least one, and the norm of f(x) is at most exp(C r(x)^tau) for every x. There is a positive constant Cprime satisfying the displayed bound for every x. One may take C plus log(2).

**Theorem 1.11 (Pass to a natural exponent).**

$$\exists C > 0 , \forall x , \operatorname{norm}\left(\operatorname{f}\left(x\right)\right) \le \operatorname{exp}\left({C} \cdot {{\operatorname{r}\left(x\right)} ^ {n} } \right)    $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.exists_norm_le_exp_mul_pow_of_rpow_bound` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For an arbitrary index type, seminormed codomain, and radii at least one, let tau be real and n natural with tau strictly less than n. If a positive constant gives an exponential norm bound with real exponent tau, a positive constant gives the displayed bound with the ordinary natural power n.

**Theorem 1.12 (Absorb a quadratic factor).**

$${r} ^ {2}  \le \operatorname{exp}\left({\frac {4} {b} } \cdot {{r} ^ {b} } \right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.sq_le_exp_const_mul_rpow` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For every positive real b and every real r at least one, the displayed bound holds. Bounding log(r) by a real power and then exponentiating absorbs the quadratic factor with the explicit constant four divided by b.

**Theorem 1.13 (Compare shifted radii).**

$$1 + r  \le {3} \cdot {( 1 + x  ) }   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.one_add_le_three_mul_one_add_of_le_two_mul_max` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For nonnegative real x and any real r at most twice max(x,1), the displayed inequality holds. It follows by bounding max(x,1) by one plus x.

**Theorem 1.14 (Rescale an exponential bound).**

$$\operatorname{exp}\left({A} \cdot {{x} ^ {tau} } \right) \le \operatorname{exp}\left({{A} \cdot {{B} ^ {tau} } } \cdot {{y} ^ {tau} } \right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.exp_mul_rpow_le_exp_mul_rpow_of_le_mul` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

Let A, B, x, y, and tau be nonnegative real numbers with x at most B times y. Monotonicity of real powers and the multiplicative power identity give the displayed comparison, with all zero boundary cases included.

**Theorem 1.15 (A larger exponent with the same floor).**

$$\exists   tau , rho < tau \land tau < \operatorname{floorNat}\left(rho\right) + 1  \land 0 \le tau \land \operatorname{floorNat}\left(tau\right) = \operatorname{floorNat}\left(rho\right)  $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.exists_between_self_and_floor_add_one_same_floor` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For each nonnegative real rho, there exists a real tau strictly between rho and its natural floor plus one. Tau is nonnegative and has the same natural floor as rho. The midpoint of that interval supplies such an exponent.

**Theorem 1.16 (Restrict growth to a sphere).**

$$\operatorname{log}\left(\operatorname{norm}\left(\operatorname{f}\left(z\right)\right)\right) \le {C} \cdot {{( 1 + \operatorname{abs}\left(R\right)  ) } ^ {rho} }   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.log_norm_le_of_log_one_add_growth_on_sphere` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For any complex function f and real C, rho, and R, assume the global bound log(1+norm(f(z))) at most C (1+norm(z))^rho for every complex z. At every point on the sphere centered at zero with radius absolute R, the displayed estimate holds. Neither C nor rho is assumed nonnegative.

**Definition 1.17 (Entire order as an epsilon family).**

$$\operatorname{EntireOfOrderAtMost}\left(rho, f\right) \iff \operatorname{Differentiable}\left(\mathbb {C} , f\right) \land \forall epsilon > 0 , \exists C > 0 , \forall z , \operatorname{norm}\left(\operatorname{f}\left(z\right)\right) \le \operatorname{exp}\left({C} \cdot {{( 1 + \operatorname{norm}\left(z\right)  ) } ^ {rho + epsilon } } \right)  $$

*Formalization.* `D5/S3/Analytic/EntireGrowth/RealExponential.EntireOfOrderAtMost` (`✓ std3`).

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For real rho and a complex function f, EntireOfOrderAtMost means complex differentiability everywhere together with the following condition: for every positive real epsilon there exists a positive real C, independent of z, bounding the norm at every complex z by exp(C (1+norm(z))^(rho+epsilon)). This definition does not identify order with a limsup or infimum definition.

**Theorem 1.18 (Differentiability of an entire-order function).**

$$\operatorname{Differentiable}\left(\mathbb {C} , f\right) $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.differentiable` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For every real rho and every complex function f satisfying EntireOfOrderAtMost rho f, the function is complex differentiable everywhere.

**Theorem 1.19 (Extract a bound at a positive margin).**

$$\exists C > 0 , \forall z , \operatorname{norm}\left(\operatorname{f}\left(z\right)\right) \le \operatorname{exp}\left({C} \cdot {{( 1 + \operatorname{norm}\left(z\right)  ) } ^ {rho + epsilon } } \right)   $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EntireGrowth/RealExponential.exists_bound` (`✓ std3`). ∎

*Citation.* Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne (2026). *Real logarithmic and exponential growth comparisons and epsilon-family entire order*. URL: <https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346>.

*Commentary.*

For every real rho, every positive real epsilon, and every complex function f satisfying EntireOfOrderAtMost rho f, there is a positive real C such that the displayed estimate holds at every complex z.

## References

- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.EntireOfOrderAtMost`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.differentiable`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.exists_between_self_and_floor_add_one_same_floor`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.exists_bound`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.exists_norm_le_exp_mul_pow_of_rpow_bound`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.exp_mul_rpow_le_exp_mul_rpow_of_le_mul`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.le_exp_of_log_one_add_le`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.le_exp_self`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_growth_of_norm_le_exp_mul_rpow`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_nonneg_mul_inv_norm_of_norm_le`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_norm_le_log_one_add_norm`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_norm_le_of_log_one_add_growth_on_sphere`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_one_add_exp_le_add_log_two`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_one_add_le_add_log_two_of_le_exp`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.log_two_le_log_two_mul_mul_inv_norm_of_norm_le`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.norm_le_exp_mul_rpow_of_exponent_le`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.norm_le_exp_mul_rpow_of_log_growth`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.one_add_le_three_mul_one_add_of_le_two_mul_max`
- Truth anchor: `D5/S3/Analytic/EntireGrowth/RealExponential.sq_le_exp_const_mul_rpow`
