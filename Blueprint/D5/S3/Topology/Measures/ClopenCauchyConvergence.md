# Full signed weak-star convergence from clopen Cauchy data

## Abstract

Clopen Cauchy values determine a represented signed weak-star whole-sequence limit under a uniform total-variation bound.

K is an arbitrary compact metric, totally disconnected Borel space, including the empty space. For a real C with 0 ≤ C and an arbitrary sequence of actual finite signed measures s, assume only the uniform total-variation bound and Cauchy convergence of s(n)(A) for every clopen A.

**Theorem 1.1 (Represented signed whole-sequence convergence criterion).**

$$\begin{aligned}\forall K: Type_{u}, [\operatorname{MetricSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{TotallyDisconnectedSpace}\left(K\right)] [\operatorname{MeasurableSpace}\left(K\right)] [\operatorname{BorelSpace}\left(K\right)] \\\forall C: \operatorname{Real}\left(\right), \forall s: \operatorname{Nat}\left(\right) \to \operatorname{SignedMeasure}\left(K\right), \\\operatorname{Nonneg}\left(C\right) \Rightarrow {\forall n: \operatorname{Nat}\left(\right), \operatorname{totalVariationRealUniv}\left(\operatorname{apply}\left(s, n\right)\right) \le C} \Rightarrow {\forall A: \operatorname{Set}\left(K\right), \operatorname{IsClopen}\left(A\right) \Rightarrow \operatorname{CauchySeq}\left(n \mapsto \operatorname{apply}\left(\operatorname{apply}\left(s, n\right), A\right)\right)}\\ \\\Rightarrow \exists mu:\operatorname{SignedMeasure}\left(K\right), \operatorname{totalVariationRealUniv}\left(mu\right) \le C \land \operatorname{Regular}\left(\operatorname{jordanPosPart}\left(mu\right)\right) \land \operatorname{Regular}\left(\operatorname{jordanNegPart}\left(mu\right)\right) \land \operatorname{Tendsto}\left(n \mapsto \operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(\operatorname{apply}\left(s, n\right)\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(mu\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/ClopenCauchyConvergence.tendsto_signedFunctional_of_clopen_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion supplies an actual SignedMeasure μ with the same real total-variation bound, regular positive and negative Jordan parts, and weak-star convergence of the represented signed functionals. There is no positivity assumption, no pre-assumed full convergence, no finite-support restriction, and no strict positivity or nonemptiness premise.

The proof first uses the existing compact metric signed subsequence theorem. On a clopen A, the characteristic locally constant function evaluates the signed functional exactly at s(n)(A). The scalar Cauchy hypothesis and the strictly monotone convergent subsequence therefore force the whole scalar sequence to converge to μ(A).

Every real locally constant function on compact K has finite range and clopen fibres. The existing vector-measure simple-function formula turns its integral into a finite sum of those clopen values, so locally constant tests converge. The existing locally constant Stone–Weierstrass closure theorem, NormedSpace.equicontinuous_TFAE, and EquicontinuousAt.tendsto_of_mem_closure extend convergence to every continuous test. The operator bound is consumed directly from NormPreservingLifts.signedFunctional_norm_le; the weak-dual evaluation criterion finishes the result. This criterion is a live helper in SignedSplitReferenceConvergence, rather than a separate new-content claim.

Regularity is inherited from the compact metric Borel finite-measure instances for the two Jordan parts. This is the analytic composition needed by the same successor/proper-limit construction. It does not construct the transfinite system, settle CH bookkeeping, or solve Talagrand Problem 8.2.

## References

- Truth anchor: `D5/S3/Topology/Measures/ClopenCauchyConvergence.tendsto_signedFunctional_of_clopen_cauchy`
- Dependency: [D5/S3/Topology/Measures/SignedWeakStarCompactness](SignedWeakStarCompactness.md)
