# Correlated forward weight ratios

## Abstract

The original forward weight ratio has quantitative value and derivative bounds.

Use the existing functions H(x)=x^(4/5) and w(x)=(1+log(x))/(x^2*log(x)^2). For x>=4 and 0<=u<=1, let A(x,u)=w(x+u*H(x))/w(x). The center in the denominator moves together with the center in the numerator.

**Theorem 1.1 (Value bounds for the price ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.price_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightControl.price_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>=3 and u>=0, the price ratio w(x+u)/w(x) is nonnegative and at most one. Positivity of the weight gives the lower bound, and monotonicity of the weight gives the upper bound.

**Theorem 1.2 (Displacement bound for the price ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.priceRatio_sub_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightControl.priceRatio_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>=4 and u>=0, the price ratio rho(x,u)=w(x+u)/w(x) satisfies 0<=1-rho(x,u)<=4*u/x. Monotonicity gives the first inequality; the lower power bound rho(x,u)>=(x/(x+u))^4 and the tangent inequality (1+v)^(-4)>=1-4*v give the second.

**Theorem 1.3 (Value of the original ratio).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.weightRatio_sub_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightControl.weightRatio_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the displacement bound at u*H(x) gives |A(x,u)-1|<=4*x^(-1/5). The lower bound uses (x/(x+u*H(x)))^4 rather than replacing the weight by a different window.

**Theorem 1.4 (Correlated derivative at a general exponent).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.priceRatio_control`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightControl.priceRatio_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For theta>0, x>=4 and s>=0, put r(x)=w(x+s*x^theta)/w(x). Then 0<=r(x)<=1 and r'(x)=r(x)*(L(x+s*x^theta)*(1+theta*s*x^(theta-1))-L(x)), where L is the logarithmic derivative of w. The derivative has absolute value at most (8+5*theta)*s*x^(theta-2). The Lipschitz bound for L contributes 8*s*x^(theta-2); the moving argument contributes 5*theta*s*x^(theta-2).

**Theorem 1.5 (Cancellation in the correlated derivative).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.weightRatio_control`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/WeightControl.weightRatio_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio satisfies 0<=A(x,u)<=1. Put L(x)=(-2+1/(1+log(x))-2/log(x))/x, the logarithmic derivative of w. The derivative of A in x equals A(x,u)*(L(x+u*H(x))*(1+(4/5)*u*x^(-1/5))-L(x)). Its absolute value is at most 12*x^(-6/5), by the general exponent estimate at theta=4/5 and u<=1.

For x>=4, |L(x)|<=5/x and |L'(x)|<=8/x^2. The mean value theorem bounds L at the two correlated arguments. Their separation is u*H(x), so the difference has size at most 8*u*x^(-6/5). The moving-endpoint factor contributes at most 4*u*x^(-6/5). This establishes the extra relative window factor in the derivative.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.priceRatio_control`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.priceRatio_sub_one`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.price_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.weightRatio_control`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/WeightControl.weightRatio_sub_one`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ProfileKernelDefs](ProfileKernelDefs.md)
- Dependency: [D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature](../OriginalEarlyDivisorQuadrature.md)
