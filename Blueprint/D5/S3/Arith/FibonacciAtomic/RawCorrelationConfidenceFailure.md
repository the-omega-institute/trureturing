# First-Gate Event Masses

## Abstract

The reverse and forward first-gate events have exact masses under the heterogeneous product law.

For rho in (0,1/8], let the first high coordinate have parameter 1-3rho and the second and third coordinates have parameter 2rho. The product mass of a Boolean triple is the product of its three Bernoulli masses. The reverse event is (false,true,true), while the forward event is (true,false,true).

**Theorem 1.1 (Exact reverse and forward event masses).**

$$\forall rho \in \mathbb{R} (0<rho\leq\frac{1}{8}), \operatorname{Mminus}\left(rho\right) = 12(rho)^{3} \land \operatorname{Mplus}\left(rho\right) = 2rho(1-3rho)(1-2rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem evaluates both event masses by the finite product sum. The reverse mass is 12 rho cubed. The forward mass is 2 rho (1-3rho) (1-2rho).

**Theorem 1.2 (Forward event sign symmetry).**

$$\forall alpha \in \mathbb{R}, \forall rho \in \mathbb{R}, \operatorname{Mplus}\left(alpha, rho\right) = \operatorname{Mminus}\left(alpha, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure.forward_sign_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the forward first-gate event, the two nonzero signed contributions have equal finite product mass. The equality follows by expanding the two remaining Boolean coordinates and the three channel labels.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure.forward_sign_symmetry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RawCorrelationConfidenceFailure.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/RawCorrelationMomentIdentities](RawCorrelationMomentIdentities.md)
