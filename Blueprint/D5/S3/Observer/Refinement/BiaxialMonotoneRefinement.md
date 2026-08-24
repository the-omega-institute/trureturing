# Biaxial Monotone Refinement

## Abstract

Enlarging either axis of a finite orbit-observation schedule can only shrink indistinguishability.

**Lemma 1.1 (More observation indices refine indistinguishability).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}J, K: \operatorname{Finset}\left(\mathbb{N}\right), m: \mathbb{N},\\{}readout: \mathbb{N} \to X \to O, T: X \to X,\\{}J \subseteq K \Rightarrow \operatorname{Indist}\left(K, m, readout, T\right) \subseteq \operatorname{Indist}\left(J, m, readout, T\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.prime_axis_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite readout-index sets J contained in K and a fixed time horizon m, the K-schedule includes every experiment in the J-schedule. Agreement under all K-indexed observations therefore implies agreement under all J-indexed observations.

The resulting relation inclusion runs from Indist K m to Indist J m: adding observation indices can distinguish additional state pairs but cannot make previously distinguishable pairs indistinguishable. No arithmetic primality assumption is needed; only inclusion of the finite index sets is used.

**Lemma 1.2 (Longer observation windows refine indistinguishability).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}J: \operatorname{Finset}\left(\mathbb{N}\right), m, n: \mathbb{N},\\{}readout: \mathbb{N} \to X \to O, T: X \to X,\\{}m \leq n \Rightarrow \operatorname{Indist}\left(J, n, readout, T\right) \subseteq \operatorname{Indist}\left(J, m, readout, T\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.time_axis_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed finite index set J and horizons m at most n, every iterate observed before time m is also observed before time n. The longer schedule therefore contains the shorter schedule.

With the indexed readout and transition map unchanged, agreement throughout the n-window implies agreement throughout the m-window. Extending the time horizon can consequently remove indistinguishable pairs but cannot add them.

**Theorem 1.3 (Joint expansion refines indistinguishability).**

$$\begin{gathered}\forall X, O: \operatorname{Type},\\{}J, K: \operatorname{Finset}\left(\mathbb{N}\right), m, n: \mathbb{N},\\{}readout: \mathbb{N} \to X \to O, T: X \to X,\\{}J \subseteq K \land m \leq n \Rightarrow \operatorname{Indist}\left(K, n, readout, T\right) \subseteq \operatorname{Indist}\left(J, m, readout, T\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.biaxial_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If J is contained in K and m is at most n, the schedule indexed by K through time n expands the schedule indexed by J through time m in both coordinates. Any state pair indistinguishable under the larger schedule is therefore indistinguishable under the smaller one.

The two refinements are independent: first restrict the observation indices at the longer horizon, then shorten the horizon at the smaller index set. Composing those two relation inclusions gives the joint biaxial inclusion.

## References

- Truth anchor: `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.biaxial_monotone`
- Truth anchor: `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.prime_axis_monotone`
- Truth anchor: `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.time_axis_monotone`
- Dependency: [D5/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity](../../ConceptDynamics/Experiment/ExperimentExpansionMonotonicity.md)
