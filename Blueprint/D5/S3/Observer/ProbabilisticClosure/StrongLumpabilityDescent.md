# Strong Lumpability Descent

## Abstract

A stochastic readout descends exactly when its pushed-forward one-step laws are constant on interface fibers.

**Theorem 1.1 (Strong lumpability is equivalent to stochastic descent).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}q: X \to B, K: X \to \operatorname{PMF}(X),\\{}\operatorname{ListTFAE}\left({[\exists kernel: \operatorname{range}(q) \to \operatorname{PMF}(\operatorname{range}(q)), \forall x: X, PMF.map(realizedReadout(q), K(x)) = kernel(realizedReadout(q)(x)), \forall x, y: X, q(x) = q(y) \Rightarrow PMF.map(realizedReadout(q), K(x)) = PMF.map(realizedReadout(q), K(y)), \forall x, y: X, realizedReadout(q)(x) = realizedReadout(q)(y) \Rightarrow PMF.map(realizedReadout(q), K(x)) = PMF.map(realizedReadout(q), K(y))]}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.strong_lumpability_descent_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state-conditioned PMF K(x) is pushed forward along the canonical realized-image readout of q. A descended Markov kernel is a function from that effective image to PMFs on the same image.

The second clause is strong lumpability: equal q-values give equal one-step observed laws. The third clause states the same condition on the subtype-valued canonical readout, making the image carrier explicit.

The proof constructs the descended row by choosing a preimage through the surjective canonical readout and proves independence of that choice from the fiber law.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.strong_lumpability_descent_tfae`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../../ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence.md)
