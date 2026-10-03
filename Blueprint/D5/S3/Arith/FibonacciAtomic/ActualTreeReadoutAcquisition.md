# Actual Tree Readout and Acquisition

## Abstract

Truthful address reports force complete positive-tree leaf acquisition and allow total membership decisions on every finite tree.

**Definition 1.1 (Actual addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Address`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Address` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Addresses are finite left/right words, including the empty root. False is left and true is right.

**Definition 1.2 (Four truthful replies).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Reply`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Reply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A report is an alpha leaf, beta leaf, branch, or absence in the same immutable ordered finite tree.

**Definition 1.3 (Unrestricted original readout).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.readout`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite address is legal without querying its prefixes. No composition, size, height, leaf count, positivity, candidate-family membership, or identity is supplied.

**Definition 1.4 (Complete leaf frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.leaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.leaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed left-to-right list contains all actual leaf addresses. Their labels are supplied by readout.

**Definition 1.5 (Actual nodes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.nodes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.nodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Preorder node addresses include each branch and leaf, beginning at the root.

**Definition 1.6 (One-leaf competitor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.flip`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.flip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Flipping an actual addressed leaf changes its label and preserves the full ordered shape.

**Definition 1.7 (Third actual substitution image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Positive`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive(U) means that an actual source T satisfies rho cubed(T)=U, with rho the native Fibonacci substitution.

**Definition 1.8 (History-only selector).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Policy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Policy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The next query or returned Boolean depends only on the selector's own chronological address-response history. Common initialization is independent of the unknown input.

**Definition 1.9 (All-input deterministic contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Strategy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Strategy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same policy starts at empty history and has a finite correct terminal execution on every finite source. Fuel witnesses pointwise termination and is not information supplied to the policy.

**Definition 1.10 (Distinct actual payment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.paid`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.paid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All requested reports, including repetitions, enter history. Each different actual address is paid once; repetitions use truthful cached reports.

**Definition 1.11 (Unique terminal execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.terminal`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pointwise totality selects a terminal history and output. Determinism makes this pair independent of the chosen successful fuel.

**Definition 1.12 (Finite deterministic cost).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.cost`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.cost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cost is the cardinality of the terminal paid address set. Internal computation, positioning and address length have no price.

**Definition 1.13 (Response-dependent excess).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.chi`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.chi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Chi is zero on both labelled leaves and one on branch and absence. It accounts for route addresses outside the complete leaf baseline.

**Definition 1.14 (Extended policy cost).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.extendedCost`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.extendedCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Any finite return pays for its different requested addresses, including wrong returns. Failure to terminate at any finite fuel has cost positive infinity.

**Definition 1.15 (Wrong-return event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.wrongReturn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.wrongReturn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A seed is wrong on a source when a finite execution returns a Boolean different from the actual image-membership bit.

**Definition 1.16 (Nontermination event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.diverges`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.diverges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A seed diverges on a source precisely when no finite-fuel execution returns.

**Definition 1.17 (Original per-source random contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.RandomContract`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.RandomContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each fixed source separately, the wrong-return and nontermination seed events are measurable and have measure zero, and the nonnegative extended cost is measurable. Null exceptional seeds are allowed. Neither completeness, measurable transcripts, nor an assumed common good-seed set is required.

**Definition 1.18 (Arbitrary seed probability space).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.RandomStrategy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.RandomStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A strategy carries its own seed type, sigma algebra, probability law and history-only policies. The seed law is independent of the input; the same seed and same history determine the same query, cache use, stop and output.

**Definition 1.19 (Literal uniform carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Seed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Seed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seed is the closed unit interval, including both endpoints, equipped with the completed Lebesgue sigma algebra.

**Definition 1.20 (Uniform seed law).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.unitSeedMeasure`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.unitSeedMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law is completed Lebesgue probability measure on the closed unit interval.

**Definition 1.21 (Uniform random contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.UniformRandomStrategy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.UniformRandomStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same per-source measurable-null-exception contract is used on the fixed uniform probability space.

**Definition 1.22 (Nonempty family maximum).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.maxOn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.maxOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

MaxOn takes the finite maximum of extended nonnegative costs over Fin(m), with m positive.

**Definition 1.23 (Own-law expectation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.randomExpected`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.randomExpected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonnegative integral uses this strategy's own input-independent seed law and allows infinite values.

**Definition 1.24 (Deterministic objective).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.D`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D(F) is the infimum of the maximum prototype cost over all globally correct total deterministic strategies.

**Definition 1.25 (Worst fixed-source expectation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.R`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R(F) is the infimum over the original arbitrary seed probability spaces of the maximum of the fixed-prototype expected extended costs.

**Definition 1.26 (Uniform fixed-source expectation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Ru`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Ru` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ru(F) restricts the preceding infimum to the fixed completed Lebesgue unit-interval seed space.

**Definition 1.27 (Shared-seed objective).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.W`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(F) integrates the maximum prototype cost at one common controller and seed, then takes the infimum over arbitrary original random strategies.

**Definition 1.28 (Uniform shared-seed objective).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Wu`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Wu` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Wu(F) uses that same shared-seed maximum and the fixed uniform seed space. None of these objectives assigns a prior to prototypes or unknown sources.

**Definition 1.29 (Full joint responses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.vector`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.vector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vector(F,u) is the complete m-coordinate tuple of actual reports at u, retaining coordinates outside any current survivor set.

**Definition 1.30 (Actual vector range).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.actualVectors`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.actualVectors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only vectors produced at actual addresses occur. A finite union of prototype nodes realizes all non-absent vectors; addresses outside it yield the common all-absent vector.

**Definition 1.31 (One-step alpha-position law).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.alphaValid`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.alphaValid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every alpha leaf is the right member of a terminal ordered pair (beta,alpha). Root alpha is excluded.

**Definition 1.32 (Two-step terminal-cherry law).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.cherryValid`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.cherryValid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every terminal cherry has the ordered labels (beta,alpha); branch descendants satisfy the same requirement.

**Definition 1.33 (Third-image source obstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.sourceLaw`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.sourceLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SourceLaw combines the one-step alpha-position and two-step terminal-cherry requirements.

**Theorem 1.34 (Leaf obstruction, rigidity and compulsory acquisition).**

$$(\forall t, (\operatorname{sourceLaw}\left(\operatorname{rhoThree}\left(t\right)\right) = true)) \land \\(\forall t, u, ((u \in \operatorname{leaves}\left(\operatorname{rhoThree}\left(t\right)\right)) \implies (\neg\operatorname{Positive}\left(\operatorname{flip}\left(\operatorname{rhoThree}\left(t\right), u\right)\right)))) \land \\(\forall V, U, ((\forall u, ((u \in \operatorname{leaves}\left(V\right)) \implies (\operatorname{readout}\left(u, U\right) = \operatorname{readout}\left(u, V\right)))) \implies (U = V))) \land \\(\forall V, u, v, (((u \in \operatorname{leaves}\left(V\right)) \land \\(v \neq u)) \implies (\operatorname{readout}\left(v, \operatorname{flip}\left(V, u\right)\right) = \operatorname{readout}\left(v, V\right)))) \land \\(\forall p, U, (((\operatorname{Strategy}\left(p\right)) \land \\(\operatorname{Positive}\left(U\right))) \implies (\operatorname{subset}\left(\operatorname{leaves}\left(U\right), \operatorname{paid}\left(\operatorname{terminalHistory}\left(p, U\right)\right)\right)))) \land \\(\forall t, (\operatorname{alphaValid}\left(\operatorname{rho}\left(t\right)\right) = true)) \land \\(\forall t, (\operatorname{cherryValid}\left(\operatorname{rhoTwo}\left(t\right)\right) = true)) \land \\(\forall policy, n, m, h, U, X, Y, (((\operatorname{execute}\left(policy, n, h, U\right) = \operatorname{some}\left(X\right)) \land \\(\operatorname{execute}\left(policy, m, h, U\right) = \operatorname{some}\left(Y\right))) \implies (X = Y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.source_foundation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual positive tree and each of its leaves, the same-shape label flip is negative and every other address report is unchanged. Third substitution images satisfy sourceLaw; single substitutions satisfy alphaValid, and double substitutions satisfy cherryValid. Matching all labelled leaves forces literal ordered-tree equality. A deterministic correct accepting run must therefore acquire every positive leaf, by replay against the negative competitor. Two successful runs of the same policy from the same history on the same input have identical terminal histories and outputs.

**Definition 1.35 (Actual frontier transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The head pending address is removed after its truthful report. A branch inserts its actual left and right children; a leaf inserts nothing.

**Definition 1.36 (Fresh acquisition frontier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.frontier`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.frontier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pending work starts at the root and is computed only from this acquisition phase's own history.

**Definition 1.37 (Actual finite traversal).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite preorder traversal records root, actual branches and leaves. It describes the execution for proof, and is not supplied to the unknown-input controller.

**Definition 1.38 (Literal transition derivation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.AcquisitionRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.AcquisitionRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inductive relation follows the acquisition frontier transitions through the chronological acquired reports.

**Definition 1.39 (Report-only reconstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.restore`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.restore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restore reads only actually acquired reports. It reconstructs a branch from both descendants and refuses missing or absent-node descriptions.

**Definition 1.40 (Finite actual preimages).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.boundedSources`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.boundedSources` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composition fibers enumerate all actual sources with at most the acquired leaf count; both root leaves remain in the finite enumeration.

**Definition 1.41 (Finite forward comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.finiteDecision`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.finiteDecision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The acquired description is positive exactly when one of those finitely many actual candidate descriptions has third substitution equal to it.

**Definition 1.42 (Global actual acquisition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionPolicy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionPolicy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This history-only policy asks for the root and expands only branch reports. Once reconstruction is complete, it decides by finite forward comparison. It has no hidden description, inverse query, or initial size bound.

**Theorem 1.43 (All finite inputs terminate with the correct decision).**

$$(\forall U, (\operatorname{finiteDecision}\left(U\right) = true \iff \operatorname{Positive}\left(U\right))) \land \\(\forall U, (\operatorname{execute}\left(acquisitionPolicy, \operatorname{length}\left(\operatorname{acquisitionTrace}\left(emptyAddress, U\right)\right)+1, emptyHistory, U\right) = \operatorname{some}\left(\operatorname{pair}\left(\operatorname{acquisitionTrace}\left(emptyAddress, U\right), \operatorname{finiteDecision}\left(U\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisition_foundation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite source U, finiteDecision(U) is true exactly when U is positive, and acquisitionPolicy from empty history executes exactly the actual finite traversal before returning that bit. Native substitution never decreases leaf count, so every actual preimage lies in the finite enumeration. This proves finite rejection as well as finite acceptance, including both negative root leaves. Traversal reconstruction uses only acquired truthful reports.

**Definition 1.44 (Independent total fallback).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.fallback`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.fallback` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fallback uses the all-input acquisition policy from its own initial state and empty logical history. It is correct and finitely terminating on every actual finite input; it is independent of a finite prototype promise.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.AcquisitionRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Address`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Policy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Positive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.R`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.RandomContract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.RandomStrategy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Reply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Ru`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Seed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Strategy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.UniformRandomStrategy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.W`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.Wu`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionPolicy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisitionTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.acquisition_foundation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.actualVectors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.alphaValid`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.boundedSources`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.cherryValid`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.chi`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.cost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.diverges`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.extendedCost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.fallback`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.finiteDecision`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.flip`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.leaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.maxOn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.nodes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.paid`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.randomExpected`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.restore`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.sourceLaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.source_foundation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.terminal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.unitSeedMeasure`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.vector`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.wrongReturn`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](GenealogicalFiberTransport.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](../../ConceptDynamics/Experiment/PassivePolicyNormalization.md)
