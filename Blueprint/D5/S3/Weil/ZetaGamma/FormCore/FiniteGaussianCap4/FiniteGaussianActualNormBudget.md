# Actual finite Gaussian norm and complete-tail budgets

## Abstract

Actual finite Gaussian norm and complete-tail budgets

For finite real c and sites a, F(x)=sum_i c(i)*exp(9*a(i)/2-exp(2*a(i))*x). Write P=finiteGaussianPartialSum(c,a,32), d(k)=finiteGaussianNormalizedCoefficient(c,a,2*k), and z(k)=normalizedCentralMellin(2*k)/normalizedCentralMellin(0). These are the actual Gaussian prefix, normalized coefficients, and central Mellin integrals. The source reflection is a coefficient-preserving permutation sending each site to its negative, not a declaration about an arbitrary even function of x.

Put HH=sum_(k<16) d(k)^2 and HT=integral_(0,infinity) x^(7/2)*(F(x)-P(x))^2 dx. Set h(k)=((2*k+9/4)^2-440)/10-3/4, E=sum_(n>=0) h(16+n)*d(16+n)^2, and S=sum_(n>=0) (2*(16+n)+9/4)^2*d(16+n)^2. The linked Lean declarations are the proof source; this exposition itself records no final-acceptance or priority claim.

**Theorem 1.1 (The physical prefix norm is the coefficient head norm).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_head_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_head_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the reflected finite source, integral_(0,infinity) x^(7/2)*P(x)^2 dx=HH. The prefix contains the ordinary modes n=0,...,31; reflection makes the odd coefficients zero, leaving precisely k=0,...,15. No zero-mass or nonvanishing premise is needed. The identity consumes the actual finite-prefix norm theorem.

**Theorem 1.2 (Exact norm splitting for the complete actual remainder).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_head_tail_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_head_tail_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same reflected finite source, integral_(0,infinity) x^(7/2)*F(x)^2 dx=HH+HT. The proof uses the actual remainder HasSum theorem and splits its complete nonnegative coefficient series at k=16. No basis-completeness, Parseval, integrability, zero-mass, or nonzero-head hypothesis is supplied by the caller.

**Theorem 1.3 (Exact energy and norm debit of every tail mode).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_tailH_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_tailH_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the reflected finite source, E=S/10-(179/4)*HT. Both complete series and the actual remainder norm are supplied by the Gaussian graph and Jacobi summability results. The coefficient 179/4 is exactly 44+3/4; no far-tail cutoff, endpoint deletion, zero-mass premise, or nonvanishing premise is introduced.

**Theorem 1.4 (Actual zero mass fixes the complete tail charge).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_zero_tail_charge`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_zero_tail_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite real Gaussian source with sum_i c(i)=0, sum_(n>=0) z(16+n)*d(16+n)=-sum_(k<16) z(k)*d(k). This declaration needs no reflection or nonvanishing hypothesis. Its proof consumes the actual central Mellin HasSum and then splits that convergent series. This source mass equation is not identified here with the distinct complete Suzuki mean-zero constraint.

**Theorem 1.5 (A uniform lower bound on the unchanged tail weight).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.cap475_tailH_ge_seventy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.cap475_tailH_ge_seventy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, 70<=h(16+n). This is a scalar polynomial inequality for the existing tailH definition. It imposes no source hypothesis and does not modify the original reciprocal-tail constant or certificate data.

**Theorem 1.6 (Seventy times the actual remainder norm is paid).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_tailH_seventy_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_tailH_seventy_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the reflected finite source, 70*HT<=E. The termwise scalar bound is summed using actual tail-energy summability and the exact actual remainder-norm HasSum. No mass-zero, global-nonzero, assumed expansion, or additional integral-domain premise is needed. These norm and charge budgets support the finite-source comparison; they alone assert neither its tail quotient nor RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.cap475_tailH_ge_seventy`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_head_norm`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_head_tail_norm`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_tailH_budget`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_tailH_seventy_norm`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget.finiteGaussian_actual_zero_tail_charge`
