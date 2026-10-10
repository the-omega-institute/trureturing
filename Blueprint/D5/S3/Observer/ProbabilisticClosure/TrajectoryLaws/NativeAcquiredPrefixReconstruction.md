# Complete acquired-prefix reconstruction

## Abstract

Every legal initialized operation prefix reconstructs its unique full native state.

run folds the literal partial nativeStep transactions from the single empty initialization. Legal(ops) means that this fold returns some state; failure is an illegal word, not a performed rejection action. PrefixForm and render are the independent concatenation grammar of ordered rejected pairs, accepted seed, completed segment words, active partial cuts, pending and delivered. reconstruct computes the original finite fields, unbounded S and acquired counts from a form. It is not the definition of execution.

**Theorem 1.1 (The actual successor matches form extension).**

$$\forall nf:PrefixForm, (\forall op:Operation, (\operatorname{nativeStep}(\operatorname{reconstruct}(nf),op)=\operatorname{map}(reconstruct,\operatorname{appendForm}(nf,op))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.reconstruct_append_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Map denotes Option.map. For every form and actual operation, folding one literal transaction from its calculated state agrees with extending the independent form and reconstructing the result. Structural induction follows every segment and each seed phase, including partial beta, fourth-segment returns and both terminal colors. Stop succeeds only at its matching pending cut.

**Theorem 1.2 (Every form executes from empty initialization).**

$$\forall nf:PrefixForm, (\operatorname{run}(\operatorname{render}(nf))=\operatorname{some}(\operatorname{reconstruct}(nf)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.run_render` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction executes the rejected pairs in their specified order, then the actual accepted pair and each payload block. The unbounded native loop theorem accounts for every beta-alpha return with its numeric banks. Completing letters perform the original writers and the next control. Pending needs no operation; delivered executes the uniquely matching Stop. Both seeds, arbitrary retry orders, arbitrary natural return counts, empty and partial words are included.

PrefixFacts specifies the exact earned state. At seed-ready the finite fields are seed none and emptyRegisters, S=0 and counts=(2p,2q), where p and q count rejected alpha-alpha and beta-beta pairs. A pending first seed letter changes only its control and its corresponding count. In an acquired payload form, let bs=completedBits, t=length(bs), w=markerWeight(bs), J=returns and e=pendingExponent. Then S=J, A=1+t-w+2p+J and B=1+2w+2q+J+e; subtraction in A is natural subtraction, with w at most t. The original completedCount is t.

The same predicate also states that Registers equals the original marker writer fold; WrittenFields gives the live seed, exact natural weight and syndrome, first-marker Z, QOne and QTwo held at bs.take(3), and the post-third bare snapshot held thereafter. The arbitrary-length total-writer invariant supplies these fields; the original four-slot bound makes the weight modulo five equal its natural sum. recoverMarkers of the actual finite fields equals bs.take(3), including both active phases and the pending or delivered terminal cut. SegmentRefinements states, for every completed segment, the existing first-completion Parses predicate on pWord(j,b), recursively for its remaining segments.

**Theorem 1.3 (Exact S, counts and written fields).**

$$\forall nf:PrefixForm, (\operatorname{PrefixFacts}(nf,\operatorname{reconstruct}(nf)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.reconstruction_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction over the independent payload form gives accumulated returns, the two paid-count equations, the original completed count and the actual writer fold. The arbitrary-length marker invariant supplies every seed and selected triple, including all-equal triples, the post-write latch and held records; the four-slot bound restores exact natural weight. Each local segment invokes the exact first-completion language theorem. At the third latch e=0 and t=3, so A=4-w+2p+J and B=1+2w+2q+J. No selected count bank or receiver delivery is assumed.

**Theorem 1.4 (Execution commutes with finite projection).**

$$\forall c:AcquiredNativeState, (\forall ops:\operatorname{List}(Operation), (\operatorname{map}(pi,\operatorname{execute}(c,ops))=\operatorname{executeFinite}(\operatorname{pi}(c),ops)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.execute_finite_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every acquired native state c and finite operation list ops, mapping the actual partial execute result by pi(d)=d.source.finiteFields equals executeFinite(pi(c),ops). The result includes illegal words on both sides as none, as well as all lawful seed, marker, fourth, pending and delivered prefixes. It follows by composing finite_projection_commutes through the original execute fold. The native reconstruction and installed full-law decoder consume this projection identity; no condition on counts or payloadReturns is added.

**Theorem 1.5 (The full native prefix theorem).**

$$\forall ops:\operatorname{List}(Operation), ((\operatorname{Legal}(ops)\Leftrightarrow(\exists! nf:PrefixForm, \operatorname{render}(nf)=ops))\land\forall nf:PrefixForm, ((\operatorname{render}(nf)=ops)\Rightarrow(\operatorname{run}(ops)=\operatorname{some}(\operatorname{reconstruct}(nf))\land\operatorname{PrefixFacts}(nf,\operatorname{reconstruct}(nf))\land\operatorname{finiteRun}(ops)=\operatorname{some}(\operatorname{pi}(\operatorname{reconstruct}(nf))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.native_acquired_prefix_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite operation word ops, legality is equivalent to existence of exactly one rendered form. Every such form gives the actually folded full state and all PrefixFacts, while the independently folded finite table yields its finite projection pi(c)=c.source.finiteFields. For the forward implication, induction on right extension of a legal word obtains its form using the proved native successor identity. The independent decoder proves uniqueness. Conversely each form executes by the initialized-run theorem. A separate induction proves projection commutation through the entire fold.

The finite fields share completed t and fixed-selector latch status with original control and snapshot: the theorem proves their original phase and writer invariants. The source keeps S and live counts even where the finite projection erases them. No retry order or marker word is a runtime archive, and no numeric bank is newly delivered by Stop. This finite-prefix theorem does not identify initialized and resumed measurable future laws. Full infinite continuations, raw/event measurable inverses, shared-depth conditioning, posterior mixtures and the subsequent coherence and rank conclusions require further results.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.execute_finite_projection`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.native_acquired_prefix_reconstruction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.reconstruct_append_form`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.reconstruction_invariants`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.run_render`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePrefixNormalForms](NativePrefixNormalForms.md)
