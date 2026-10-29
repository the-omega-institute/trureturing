# Inverse coordinates for the original Mellin adjoint

## Abstract

The original forward Mellin adjoint admits an exact inverse-coordinate representation.

**Theorem 1.1 (Exact change of variables in the Mellin adjoint).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/InverseTransport.adjointKernel_inverse_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/InverseTransport.adjointKernel_inverse_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0>=4 and t>=max(8,B(x0)), let x(t,z) be the positive solution of t=x+z*x^(4/5), and let D=1+(4/5)*z*x^(-1/5). Then the actual adjoint q_s(t), defined by integrating x^(-s-1)*k(x,t) over x>=x0, equals the integral over z in [0,1] of x(t,z)^(-s-1/2)*integral(w(x+u*x^(4/5))/w(x),u=z..1)/D.

The original support reduces the center integral to [x(t,1),t]. The exact derivative x_z=-x^(4/5)/D gives the change of variables. Integrating the price derivative w=-lambda' on the same window produces the inner weight ratio; x^(8/5)/x^(11/10)=sqrt(x) then gives the principal Mellin exponent.

**Theorem 1.2 (Identification with the normalized triangular adjoint).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/InverseTransport.adjointKernel_eq_inverseAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/InverseTransport.adjointKernel_eq_inverseAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x0>=4 and t>=max(8,B(x0)), the actual Mellin adjoint equals the normalized triangular adjoint used for the uniform remainder estimates. The equality follows from the exact inverse-coordinate integral and Fubini on the fixed triangle.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/InverseTransport.adjointKernel_eq_inverseAdjoint`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/InverseTransport.adjointKernel_inverse_coordinates`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Adjoint](Adjoint.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Asymptotic](Asymptotic.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/Remainder](Remainder.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightControl](WeightControl.md)
