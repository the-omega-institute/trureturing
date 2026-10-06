# Finite Heterogeneous Raw-Correlation Moments

## Abstract

The heterogeneous first-window parameters are legal and have an exact finite disagreement mass and norm-gap identity.

For rho in (0,1/8], set H1=1-3rho, H2=L3=2rho. The three coordinates are independent Bernoulli variables with these parameters. The product expectation is the explicit sum over all eight Bool triples of the disagreement indicator: it is one exactly when the first two coordinates differ and the third coordinate is true. The theorem evaluates this finite law exactly. For a positive channel strength alpha, the resulting raw-score mean is also evaluated.

**Theorem 1.1 (Legal parameters and exact finite moments).**

$$\forall rho, alpha \in \mathbb{R} (0<rho\leq\frac{1}{8} \land 0<alpha), \begin{aligned}0\leq\operatorname{H}\left(1, rho\right)\leq1 \land 0\leq\operatorname{H}\left(2, rho\right)\leq1 \land 0\leq\operatorname{L}\left(3, rho\right)\leq1 \land\\\operatorname{d}\left(rho\right) = 2rho(1-5rho+12(rho)^{2}) \land\\\operatorname{G}\left(rho\right) = -2rho+10(rho)^{2} \land\\\operatorname{M}\left(alpha, rho\right) = 3alpharho(rho)^{2} \land0<\operatorname{M}\left(alpha, rho\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first six conjuncts state that H1, H2 and L3 are probabilities. The seventh is the exact disagreement mass d=2rho(1-5rho+12rho^2), the last is the squared-norm difference H2 L3-H1 L3=-2rho+10rho^2, and the score mean alpha/8 times their sum is 3alpha rho^3>0.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities.result`
