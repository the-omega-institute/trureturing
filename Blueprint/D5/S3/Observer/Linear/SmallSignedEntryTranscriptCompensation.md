# Small signed entry compensation and exact acquisition

## Abstract

Small signed entry compensation and exact acquisition

A native source s has positive finite order M, a rational symmetric tridiagonal matrix A, strictly positive adjacent links, and a distinguished first coordinate. For every real vector v, its quadratic form lies between one quarter and three quarters of the squared Euclidean norm. There is no common bound on order and no positive lower bound on links. An entry z is a rational vector. InBall(rho,z) means rho is nonnegative and the sum of the real squares of z is at most rho squared.

Commands are Read, Tick, Hold, and Add(u) for rational u. Read returns the current first coordinate. Tick replaces x by Ax and returns the new first coordinate. Add(u) replaces x by x+u e0 and returns a fixed acknowledgement; Hold leaves x unchanged and gives the same acknowledgement. The function run records every return in chronological order. The function finalState records the field after the whole word. The reference is the one-cell matrix [1/2] with zero entry.

**Theorem 1.1 (One fixed small entry for a complete word).**

$$\forall rho\in \mathbb{Q}, rho>0, \forall w\in List\left(Command\right), \exists epsilon, s, z: 0<epsilon\le\frac{1}{8}\land order\left(s\right)=t\left(w\right)+2\land InBall\left(rho, z\right)\land \sum_{i}|z\left(i\right)|<rho\land run\left(S, z, w\right)=run\left(reference, 0, w\right)\land S^{2}_{0,0}=(\frac{1}{2})^{2}+epsilon^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.small_entry_complete_transcript_compensation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive rational radius and every finite command word, one fixed source and entry reproduce the reference's entire list of scalar returns and acknowledgements. Here t(w) counts actual Ticks, and S is the matrix of s. The witness has order t(w)+2, positive first link epsilon at most 1/8, diagonal 1/2, and all remaining links 1/8. The sum of absolute entry coordinates is strictly below the radius, hence so is the Euclidean norm.

Normalize the weak first edge so that its upper entry is one and its lower entry is X. The root-return perturbation is divisible by X, while the observation pivots at distance j are the constant (1/8)^(j-1). Substitution X=epsilon squared converts the return perturbation into order epsilon squared and off-root observations into order epsilon. Solving the polynomial triangular system therefore gives z_i=epsilon W_i(epsilon squared). A coefficient bound and a rational choice of epsilon make this one entry arbitrarily small.

The word demand is computed chronologically: each Add contributes its return discrepancy and each Tick shifts the remaining ages. Induction preserves every Read and every post-update Tick return, including repeated Adds at one epoch. Zero Ticks and zero compensating polynomials are included. A controller receiving these same returns makes the same local decisions and successful export.

**Theorem 1.2 (Deterministic exact acquisition is impossible at positive radius).**

$$\forall rho\in \mathbb{Q}, rho>0, \forall L, E, \forall p\in Controller\left(L, E\right), \forall initial\in L, \forall target\in AcquisitionTarget\left(E\right), \neg AcquiresOnBall\left(rho, p, initial, target\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.no_deterministic_exact_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L and E are arbitrary local-state and export types. A controller p:L to Decision(L,E) can compute locally, call a native command and branch on its reply, or halt with an export. It has no source argument or source-dependent advice. AcquiresOnBall requires a finite successful execution on every admitted source and entry, and requires every successful export to satisfy the chosen target at its actual final field.

The target is either exact native order, the entire impulse sequence (A^j)00, or the complete reply function of every finite legal continuation from the actual final field. Native order is a necessary component of exact native-law acquisition. A complete reply function is a necessary component of a self-sufficient stateful predictor, so these obstructions also exclude those stronger tasks. No effectiveness restriction or finite-state restriction is imposed on the local types.

Replay a successful reference execution on the fixed compensating source. Its order differs and its second impulse moment differs. For the predictor target, compare the alternative continuations Tick;Tick and Add(1);Tick;Tick from each actual final field. The difference between their last scalars is the source's second moment. Both alternatives cannot agree across the two sources. These are alternative hypothetical continuations, with no reset or copying operation required.

**Theorem 1.3 (Zero-error fair-bit acquisition is impossible).**

$$\forall rho\in \mathbb{Q}, rho>0, \forall L, E, \forall p\in BitController\left(L, E\right), \forall initial\in L, \forall target\in AcquisitionTarget\left(E\right), \neg FairAcquiresOnBall\left(rho, p, initial, target\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.no_fair_zero_error_exact_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A BitController additionally requests the next independent fair bit. A successful execution records its finite consumed bit prefix, finite command word, and export; arbitrary local computations between requests are allowed. The tape space is the infinite Bool product with its fair product measure. A tape belongs to finiteSuccess exactly when some successful finite execution uses a prefix of that tape. The event errorEvent additionally requires an incorrect export at the actual final field.

FairAcquiresOnBall requires, separately on every fixed source and admitted entry, that the complement of finiteSuccess and the event errorEvent both have measure zero. Nontermination and unsuccessful runs are outside successful acquisition. Each fixed prefix cylinder has measure 2 to the negative prefix length, including mass one for the empty prefix.

Almost-sure reference success supplies one successful finite execution. Its positive-mass cylinder and zero error force that fixed export to be correct on the reference. Construct one compensating source from its command word and then fix this source. The same bit prefix and replies replay the execution on this source, where the export cannot be correct. Its whole positive-mass cylinder is an error event. The construction gives no uniform positive lower bound on error independent of the controller, radius, or transcript.

## References

- Truth anchor: `D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.no_deterministic_exact_acquisition`
- Truth anchor: `D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.no_fair_zero_error_exact_acquisition`
- Truth anchor: `D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.small_entry_complete_transcript_compensation`
- Dependency: [D5/S0/Naming/GreenClassMeasure](../../../S0/Naming/GreenClassMeasure.md)
