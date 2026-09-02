# State and Record Readout Distinguishability

## Abstract

Equal endpoints collapse under state readouts; record separation is exactly output inequality.

**Theorem 1.1 (State readouts merge; record readouts separate conditionally).**

$$\forall Gamma, X, Lambda_{1}, Y, Y_{2}: \operatorname{Type},\ e: Gamma \to X, r: Gamma \to Lambda_{1}, q_{2}: Lambda_{1} \to Y_{2},\ gamma, gammaPrime: Gamma, x: X, lambda, lambdaPrime: Lambda_{1},\ (e\left(gamma\right) = x \land e\left(gammaPrime\right) = x \land r\left(gamma\right) = lambda \land r\left(gammaPrime\right) = lambdaPrime \land lambda \neq lambdaPrime) \Rightarrow\ (\forall s: X \to Y, s\left(e\left(gamma\right)\right) = s\left(e\left(gammaPrime\right)\right)) \land\ (\neg \operatorname{ker}\left(q_{2} \circ r, gamma, gammaPrime\right) \iff \left(q_{2}\right)\left(lambda\right) \neq \left(q_{2}\right)\left(lambdaPrime\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two histories have the same endpoint x and respective record images lambda and lambdaPrime, with the record images distinct. The endpoint and record-image maps use the repository's canonical generic Concept readout carrier.

The first public conjunct quantifies over every state-only readout s. Since both histories end at x, their state readout values are equal.

The second public conjunct is an equivalence. The composed history readout q2 after the record-image map lies outside its equality kernel exactly when q2(lambda) and q2(lambdaPrime) differ. Thus its two directions are the source's two record-separation assertions.

The theorem does not claim that q2 separates every pair of distinct records. A constant q2 makes both sides of the equivalence false, as required by the source's conditional wording.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../../ConceptDynamics/ConceptFiberDecomposition.md)
