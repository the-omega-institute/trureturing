# Distribution-Independent Closure

## Abstract

Distribution-independent readout closure is equivalent to deterministic depth-zero closure.

**Theorem 1.1 (Distribution-independent closure criterion).**

$$\begin{gathered}\tau: Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}\operatorname{Eff}(K) \iff (\forall \mu: \operatorname{PMF}(Y), q_{*}(\tau_{*}(\mu)) = K_{*}(q_{*}(\mu))),\\{}\operatorname{Fac}(\Sigma) \iff (\forall y, q(\tau(y)) = \Sigma(q(y))),\\{}(\exists K: O \to \operatorname{PMF}(O), \operatorname{Eff}(K) \iff \exists \Sigma: O \to O, \operatorname{Fac}(\Sigma)) \land\\{}(\exists \Sigma: O \to O, \operatorname{Fac}(\Sigma) \iff m_{*} = 0) \land\\{}(\forall K: O \to \operatorname{PMF}(O), \operatorname{Eff}(K) \Rightarrow \exists! \Sigma: O \to O, \operatorname{Fac}(\Sigma) \land \forall o, K(o) = \delta_{\Sigma(o)}) \land\\{}(\exists K: O \to \operatorname{PMF}(O), \operatorname{Eff}(K) \Rightarrow \exists! K: O \to \operatorname{PMF}(O), \operatorname{Eff}(K)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/DistributionIndependentClosure.distribution_independent_closure_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a nonempty finite state carrier, let tau update its states, and let q map Y surjectively onto the actual readout carrier O. A kernel is effective when it advances the q-pushforward of every initial probability mass exactly as q after tau does.

An effective kernel exists exactly when q is a deterministic factor: there is a readout update sigma satisfying q(tau(y)) = sigma(q(y)) for every state. This is also equivalent to equality of the depth-zero and depth-one future-word relations, hence to the existing least stability depth being zero.

Applying the evolution law to point masses makes each kernel row at q(y) the point mass at q(tau(y)). Surjectivity reaches every readout, so the factor update associated with an effective kernel is unique, every effective kernel is deterministic on every readout, and the effective kernel itself is unique whenever one exists.

The proof imports the observer family's canonical future-word stability depth and uses Mathlib probability mass map and bind laws. No duplicate future relation, depth, or determinism-by-definition is introduced.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/DistributionIndependentClosure.distribution_independent_closure_criterion`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](../Separation/FiniteObservationRefinementBound.md)
