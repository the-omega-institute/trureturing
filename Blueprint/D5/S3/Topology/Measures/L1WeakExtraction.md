# Weak extraction through Hilbert approximation

## Abstract

Bounded Hilbert approximations yield weak subsequences in complete real normed spaces.

The weak convergence below tests every continuous real linear functional. No separability assumption is imposed on either ambient space, and the zero space is included. The maps denoted apply in the formulas are ordinary function evaluation.

**Theorem 1.1 (A common subsequence for countably many bounded Hilbert sequences).**

$$\begin{aligned}\forall H: Type_{v}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{RealInnerProductSpace}\left(H\right)] [\operatorname{CompleteSpace}\left(H\right)] \\\forall t: \operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right) \to H, \forall R: \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), {\forall m: \operatorname{Nat}\left(\right), \forall n: \operatorname{Nat}\left(\right), \operatorname{norm}\left(\operatorname{apply}\left(\operatorname{apply}\left(t, m\right), n\right)\right) \le \operatorname{apply}\left(R, m\right)} \Rightarrow\\\exists j:\operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right), \exists q:\operatorname{Nat}\left(\right) \to H, \operatorname{StrictMono}\left(j\right) \land \forall m: \operatorname{Nat}\left(\right), \forall phi: \operatorname{ContinuousRealLinearFunctional}\left(H\right), \operatorname{Tendsto}\left(n \mapsto \operatorname{apply}\left(phi, \operatorname{apply}\left(\operatorname{apply}\left(t, m\right), \operatorname{apply}\left(j, n\right)\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{apply}\left(phi, \operatorname{apply}\left(q, m\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1WeakExtraction.exists_common_weak_subsequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The countable family t(m,n) lies in the closed span of its range indexed by Nat × Nat. That closed span is complete and separable. Riesz representation sends each bounded row into a compact metrizable weak dual ball. Sequential compactness of the countable product gives one increasing selector for all rows. Riesz representation and symmetry of the real inner product turn convergence of dual evaluations into convergence against every functional. Restricting an ambient functional to the closed span then gives the stated conclusion. No continuity from the weak dual topology to the norm topology is asserted.

**Theorem 1.2 (Uniform norm approximation produces a genuine weak limit).**

$$\begin{aligned}\forall X: Type_{u}, [\operatorname{NormedAddCommGroup}\left(X\right)] [\operatorname{RealNormedSpace}\left(X\right)] [\operatorname{CompleteSpace}\left(X\right)] \\\forall H: Type_{v}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{RealInnerProductSpace}\left(H\right)] [\operatorname{CompleteSpace}\left(H\right)] \\\forall T: \operatorname{ContinuousRealLinearMap}\left(H, X\right), \forall f: \operatorname{Nat}\left(\right) \to X, \forall t: \operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right) \to H, \\\forall R: \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), \forall delta: \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), {\forall m: \operatorname{Nat}\left(\right), \forall n: \operatorname{Nat}\left(\right), \operatorname{norm}\left(\operatorname{apply}\left(\operatorname{apply}\left(t, m\right), n\right)\right) \le \operatorname{apply}\left(R, m\right)} \Rightarrow\\\operatorname{Tendsto}\left(delta, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right) \Rightarrow\\{\forall m: \operatorname{Nat}\left(\right), \forall n: \operatorname{Nat}\left(\right), \operatorname{norm}\left(\operatorname{apply}\left(f, n\right) - \operatorname{apply}\left(T, \operatorname{apply}\left(\operatorname{apply}\left(t, m\right), n\right)\right)\right) \le \operatorname{apply}\left(delta, m\right)} \Rightarrow\\\exists j:\operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right), \exists v:X, \operatorname{StrictMono}\left(j\right) \land \forall phi: \operatorname{ContinuousRealLinearFunctional}\left(X\right), \operatorname{Tendsto}\left(n \mapsto \operatorname{apply}\left(phi, \operatorname{apply}\left(f, \operatorname{apply}\left(j, n\right)\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{apply}\left(phi, v\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1WeakExtraction.exists_weak_subsequence_of_hilbert_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The errors delta(m) tend to zero uniformly in the sequence index; their nonnegativity follows from the norm bounds. Apply the common Hilbert selector and transfer each row through T. Hahn–Banach gives a functional of norm at most one that norms the difference of any two row limits, including a zero difference. Passing the uniform approximation bound to its scalar limit shows that the row limits are norm Cauchy. Completeness gives their norm limit; a three-term estimate proves convergence of the selected original sequence against an arbitrary functional. This is the weak-extraction mechanism for hard truncations in real L1 over a finite measure. It does not construct the disjoint carriers of subsequence splitting or resolve the signed CH construction or Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1WeakExtraction.exists_common_weak_subsequence`
- Truth anchor: `D5/S3/Topology/Measures/L1WeakExtraction.exists_weak_subsequence_of_hilbert_approximation`
