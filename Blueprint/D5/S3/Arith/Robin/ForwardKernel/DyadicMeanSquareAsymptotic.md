# Dyadic mean-square asymptotic and point extraction

## Abstract

The moving-length mean-square limit transfers to the original forward response and yields a point in every sufficiently large dyadic interval.

Write E(x)=psi(x)-x, H(x)=x^(4/5), and P(h,x)=h^(-2) times the integral of E(x+u)-E(x) for 0<=u<=h. The scale is S(X)=X^(1/5)*log(X). The assumptions are the von Koch bound, the uniform short-interval mean-square bound, and the uniform cumulative variance band asymptotic.

**Theorem 1.1 (The point-extraction weight).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.dyadic_point_weight_integral_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.dyadic_point_weight_integral_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral of x^(1/5)*log(x)/x over [X,2X], divided by S(X), tends to 5*(2^(1/5)-1). Substitution x=X*v makes the quotient the integral of v^(-4/5) over [1,2], plus the fixed integral of v^(-4/5)*log(v) divided by log(X).

**Theorem 1.2 (Transfer to the original forward response).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.forward_kernel_dyadic_mean_square_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.forward_kernel_dyadic_mean_square_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the von Koch error bound, the uniform short-interval mean-square bound, and the uniform cumulative variance band asymptotic. The moving-length theorem gives the limit (2^(1/5)-1)/3 for the normalized square integral of P(H(x),x). The integral of forwardResponse(x)^2/x has the same normalized limit. The unweighted response is sqrt(x)*P(H(x),x). After division by sqrt(x), the difference from the original response has normalized squared integral tending to zero. The L2 reverse triangle inequality therefore preserves the mean-square limit. The three hypotheses are assumptions; the von Koch bound and the short-interval estimate follow from the Riemann hypothesis, and the cumulative variance asymptotic follows from the Riemann hypothesis together with the strong pair-correlation conjecture, so the theorem is conditional.

**Theorem 1.3 (A point in each sufficiently large dyadic interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.forward_kernel_dyadic_point`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.forward_kernel_dyadic_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the von Koch bound and the two uniform variance hypotheses, the normalized integral of forwardResponse(x)^2/x tends to (2^(1/5)-1)/3. For every 0<c<1/sqrt(15), every sufficiently large interval [X,2X] contains a point x with absolute response at least c*x^(1/10)*sqrt(log(x)). Otherwise squaring and integrating the pointwise strict bound would bound the mean square by c^2 times the point-extraction weight, contradicting their limiting ratio 1/15. The three hypotheses are assumptions; the von Koch bound and the short-interval estimate follow from the Riemann hypothesis, and the cumulative variance asymptotic follows from the Riemann hypothesis together with the strong pair-correlation conjecture, so the theorem is conditional.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.dyadic_point_weight_integral_tendsto`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.forward_kernel_dyadic_mean_square_asymptotic`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.forward_kernel_dyadic_point`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper](DyadicMeanSquareUpper.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare](MovingLengthMeanSquare.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightRemoval](WeightRemoval.md)
