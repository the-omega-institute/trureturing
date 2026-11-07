# Fixed-length triangular mean square

## Abstract

Uniform short-interval variance estimates give the fixed-length triangular mean-square asymptotic.

Let E be a measurable real function bounded on every compact interval, D_u(x)=E(x+u)-E(x), B_h(x)=integral from zero to h of D_u(x), and P_h(x)=B_h(x)/h^2. Assume a uniform short-interval square bound of order theta*X^2*log(2/theta)^2 for relative increments, and cumulative variance asymptotic Y*u*log(Y/u), uniformly for Y^(3/4)<=u<=Y^(7/8).

**Theorem 1.1 (Negligible perturbations preserve normalized square limits).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.interval_square_tendsto_of_l2_negligible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.interval_square_tendsto_of_l2_negligible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f and g be square integrable on ordered intervals whose endpoints depend on X, and let S(X) be eventually positive. If the square integral of g divided by S tends to a nonnegative L and that of f-g divided by S tends to zero, then the square integral of f divided by S also tends to L. The reverse triangle inequality first compares the square roots, then squaring recovers the limit.

**Theorem 1.2 (The triangular overlap constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.fixed_length_triangular_mean_square_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.fixed_length_triangular_mean_square_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 1<=a<b<=2 and c>0. With h=c*X^(4/5) and ell=log(X/h), the integral of P_h(x)^2 over [a*X,b*X], divided by (X/h)*ell, tends to (b-a)/3 as X tends to infinity.

Cut the length integral at U=X^(31/40). The short-interval bound makes the square mass of B_U, divided by X*h^3*ell, tend to zero. Above U, the uniform cumulative variance estimate bounds each normalized covariance in absolute value by sixteen. Fubini expresses the retained square mass as an integral of these covariances on the unit square, with both coordinates restricted above U/h. Since U/h tends to zero, fixed-length covariance convergence and dominated convergence give the integral of (b-a)*min(s,t), equal to (b-a)/3. The interval L2 reverse triangle inequality restores the discarded primitive, and division by h^4 gives the stated normalization. The conclusion is conditional on the two variance hypotheses for E.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.fixed_length_triangular_mean_square_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare.interval_square_tendsto_of_l2_negligible`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance](FixedLengthCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer](VarianceTransfer.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs](VarianceTransferDefs.md)
