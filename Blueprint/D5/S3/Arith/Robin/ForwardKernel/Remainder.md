# Inverse coordinates for the forward Robin kernel

## Abstract

Inverse coordinates preserve the original forward window and its quantitative derivative scale.

Write H(x)=x^(4/5). For t>0 and z>=0, x(t,z) is the unique positive solution of t=x+z*H(x). A globally increasing extension x+z*H(max(x,0)) defines the inverse without changing this positive solution.

**Theorem 1.1 (The inverse coordinate stays within the original scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Remainder.coordinate_scale_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Remainder.coordinate_scale_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t>=1 and 0<=z<=1, 0<x(t,z)<=t and 0<=1-x(t,z)/t<=t^(-1/5). For t>=2 the additional bound x(t,z)>=t/2 holds.

**Theorem 1.2 (Differentiating the relative coordinate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Remainder.coordinate_fraction_derivative_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Remainder.coordinate_fraction_derivative_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put D=1+(4/5)*z*x(t,z)^(-1/5). The exact time derivative is x_t=1/D. After dividing by t, the constant main term cancels: (x/t)_t=z*H(x)/(5*t^2*D). Thus 0<=(x/t)_t<=t^(-6/5)/5 for t>=1 and 0<=z<=1.

**Theorem 1.3 (The relative complex Mellin power).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Remainder.normalizedPower_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Remainder.normalizedPower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p=-s-1/2 define P(t,z,s)=exp(p*log(x(t,z)/t)). For t>=2 and 0<=z<=1, its norm is at most exp(2*|p|), and |P-1|<=2*|p|*exp(2*|p|)*t^(-1/5). The logarithmic estimate |log(x/t)|<=2*t^(-1/5) retains the exact moving coordinate.

**Theorem 1.4 (The time derivative of the relative power).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Remainder.normalizedPower_derivative_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Remainder.normalizedPower_derivative_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The time derivative satisfies |P_t|<=2*|p|*exp(2*|p|)*t^(-6/5). This differentiates the relative coordinate after extracting the principal power t^p.

**Theorem 1.5 (The inverse Jacobian).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Remainder.jacobianFactor_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Remainder.jacobianFactor_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For J=1/D, 0<J<=1 and |J-1|<=2*t^(-1/5) throughout t>=2 and 0<=z<=1.

**Theorem 1.6 (The Jacobian derivative).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/Remainder.jacobianFactor_derivative_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/Remainder.jacobianFactor_derivative_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact derivative is J_t=(4/25)*z*x^(-6/5)*J^3. The bound x>=t/2 gives |J_t|<=t^(-6/5).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Remainder.coordinate_fraction_derivative_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Remainder.coordinate_scale_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Remainder.jacobianFactor_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Remainder.jacobianFactor_derivative_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Remainder.normalizedPower_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/Remainder.normalizedPower_derivative_bound`
- Dependency: [D5/S3/Arith/Robin/OriginalMovingWindowMoment](../OriginalMovingWindowMoment.md)
