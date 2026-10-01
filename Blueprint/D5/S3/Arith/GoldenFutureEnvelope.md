# Golden Future Envelope

## Abstract

The maximum priced divisor benefit over positive multiples is the least upper envelope that decreases under multiplication by a prime.

For a positive real price lambda, let goldenResourceObjective(lambda,n) be log(sigma(n)/n) minus lambda times log(n) on positive integers. Define goldenFutureEnvelope(lambda,n) as the supremum of these objectives over all positive multiples of n. This supremum is attained by a positive multiple, so it is a maximum.

**Theorem 1.1 (The least safe envelope).**

$$\forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \left(\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow goldenResourceObjective\left(lambda, n\right) \le goldenFutureEnvelope\left(lambda, n\right)\right) \land \left(\left(\forall p \in \mathbb{N},\; Prime\left(p\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow goldenFutureEnvelope\left(lambda, p \cdot n\right) \le goldenFutureEnvelope\left(lambda, n\right)\right)\right) \land \left(\forall U \in (\mathbb{N} \to \mathbb{R}),\; \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow goldenResourceObjective\left(lambda, n\right) \le U\left(n\right)\right) \Rightarrow \left(\left(\forall p \in \mathbb{N},\; Prime\left(p\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow U\left(p \cdot n\right) \le U\left(n\right)\right)\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow goldenFutureEnvelope\left(lambda, n\right) \le U\left(n\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenFutureEnvelope.golden_future_envelope_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime(p) means that p is a prime natural number. The envelope majorizes the current objective and does not increase when any prime is multiplied into a positive integer. Every other function with both properties is at least this envelope at every positive integer.

If n divides a positive integer m, write m=nq. Induction over the prime factors of q extends the prime-step inequality to U(m)<=U(n). At a maximizing multiple m, the objective is at most U(m), hence at most U(n). Self-majorization follows by including n among its own multiples, and envelope monotonicity follows by inclusion of the sets of positive multiples.

The domain includes all positive integers and all prime factors, with no restriction on the order in which factors are multiplied.

## References

- Truth anchor: `D5/S3/Arith/GoldenFutureEnvelope.golden_future_envelope_least`
- Dependency: [D5/S3/Arith/GoldenFutureExtensionMaximum](GoldenFutureExtensionMaximum.md)
