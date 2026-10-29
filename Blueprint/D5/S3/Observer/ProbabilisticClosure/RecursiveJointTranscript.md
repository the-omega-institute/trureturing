# Recursive joint residuals and adaptive transcripts

## Abstract

Recursive refinement of complete typed source rows preserves every finite acquired adaptive transcript law.

An interface specifies source states and observations at each type, parameterized actions between types, and action-specific events, records and terminals. A source supplies its actual observation, legal domain, normalized legal rows and a declared refusal event, terminal and record for every illegal attempt. The total row uses the legal row on its legal domain and a point mass on that refusal triple elsewhere.

The zero residual is equality of actual current observations. Each next residual retains the preceding relation and compares legality and the entire joint row for every same-type action. Only successful successors are replaced by their preceding residual classes. Events, records and individual typed terminal identities are preserved. Taking the realized image of this output projection changes no equality of joint rows: projection back to the output carrier recovers the usual quotient pushforward.

A policy receives the remaining horizon, current interface observation, acquired archive and full ordered history. Its selector returns a probability distribution on stopping or parameterized typed actions. Selected actions satisfy its declared permission predicate. Archive updates may use the entire acquired prefix and each new complete block of acquired tokens; the selector has no source-state, quotient-class or probability-table argument. Source legality remains part of the total row, so a permitted attempt can still produce an explicit source refusal.

Execution appends the actual observation before selection. A selected action is recorded, then its complete source row is sampled. The event and record are appended and written into the archive before a successful successor continues. A fixed terminal ends execution and is recorded distinctly. Stopping and exhaustion have separate tags. Thus run is an independently constructed probability mass function on full ordered histories, rather than a supplied transcript-law table.

**Theorem 1.1 (Recursive residuals preserve finite adaptive laws).**

$$\forall T: Interface, S: \operatorname{Source}\left(T\right), C: \operatorname{Type}, n: \mathbb{N}, i: \operatorname{Ty}\left(T\right), z, w: \operatorname{State}\left(T, i\right), \operatorname{residual}\left(S, n, i, z, w\right) \Rightarrow \forall d: \mathbb{N}, d \leq n \Rightarrow \forall P: \operatorname{Policy}\left(T, C\right), c: C, h: \operatorname{List}\left(\operatorname{Token}\left(T\right)\right), \operatorname{run}\left(S, P, d, i, z, c, h\right) = \operatorname{run}\left(S, P, d, i, w, c, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/RecursiveJointTranscript.recursive_residual_preserves_adaptive_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interfaces, source, archive type, residual depth and smaller execution depth are arbitrary. The two initial states have the same interface type and recursive residual class. Initial archives and acquired prefixes match. The conclusion compares full probability mass functions, including every ordered correlation, for every policy with the declared acquired inputs.

Induction anchors observations at depth zero. At the next depth the selectors receive equal observations and identical acquired inputs. For each selected action the induction hypothesis makes its full continuation law constant on the preceding successor classes, uniformly in the newly written archive. The realized-image factorization criterion factors this continuation through the joint output projection. Binding it against equal projected source rows proves the step, retaining event-record-successor correlations and each fixed terminal.

`D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.realized_image_unique_factorization_iff_reverse_kernel` supplies the realized-image factor directly. The finite adaptive induction supplies the continuation invariance.

All finite policies use the same typed action menu and interpreter. Finite prefixes are obtained by truncating execution; an acquired-history continuation uses that same interpreter after the prefix. The result therefore applies to every experiment in any declared family closed under these legal operations. No same-level lumpability is required. The discrete PMF argument also covers arbitrary finite or countable actual common sources, stochastic rows with zeros, multiple interfaces and actions, and unbounded acquired archive carriers.

This is the positive implication from recursive joint residuals to finite transcript-law equivalence. It does not prove its converse, identify hidden states from equal observations, give an observer a full law table, establish one-run certification, or assert realization of every completion thread. Conditional identifiability, acquisition and physical claims require their separate contracts.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.realized_image_unique_factorization_iff_reverse_kernel`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/RecursiveJointTranscript.recursive_residual_preserves_adaptive_law`
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization](../../ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.md)
