# Exact actual-history installation of native payloads

## Abstract

NativePayloadHistoryInstallation

**Theorem 1.1 (Finite literal and positive records determine the whole payload).**

$$\forall I: Type, (\forall E: \operatorname{MixedExpr}\left(I\right), (\forall loc: I \to Address, (\forall p: Address, (\forall U: Source, (\forall z: I \to Source, ((\forall i: I, ((i \in \operatorname{names}\left(E\right)) \implies (\operatorname{subtree}\left(\operatorname{loc}\left(i\right), U\right) = \operatorname{some}\left(\operatorname{z}\left(i\right)\right)))) \implies ((\operatorname{Holds}\left(U, \operatorname{compile}\left(loc, p, E\right)\right)) \iff (\operatorname{subtree}\left(p, U\right) = \operatorname{some}\left(\operatorname{eval}\left(z, E\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation.payload_history_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source is the native free ordered binary tree on alpha and beta. Native substitution sends alpha to beta and beta to the ordered pair (beta, alpha), and preserves pairs. A MixedExpr contains finite ground trees, a fixed natural substitution power of a named generator, and ordered pairs. The same generator name has one value throughout the expression.

A literal record retains a natural epoch, an original address and one of the four ordinary replies. A positive record retains two epochs and two original addresses. Its independent native semantics requires both endpoints to be reached in the same actual source and their entire subtrees to agree. Holds conjoins the supplied finite list without removing repetitions. No record is interpreted by referring to the desired payload value.

The compiler traverses the finite syntax at the supplied payload root p. An explicit pair emits its branch literal and recurses at the original left and right addresses. A ground emits the existing acquisitionTrace, including every constructor and terminal leaf. A decorated generator emits one positive link from the payload position at epoch zero to its supplied locator at that fixed epoch. Compilation receives neither the actual source nor the generator valuation.

names lists the generator occurrences, including repeated names. The only premise identifies each occurring generator at its actual original locator in U. Unused names impose no premise. The generator type need not be finite or inhabited, locator addresses need not be distinct or prefix-free, and the payload root may be empty. NativeDepthPatterns.original_present_transport gives the recorded-epoch value of each originally reached generator.

The conclusion is an exact equivalence between the generated history and the reached payload subtree with the interpreted value. The proof first establishes exact ground-trace reconstruction, using the unconditional native address-composition and root-readout clauses of ActualLeafHistoryRigidity.actual_address_geometry. Structural induction then combines ordered child reconstruction and the original generator transport. Terminal ground leaves forbid hidden extra descendants.

Overlap between payload and generator addresses is allowed. It can make both sides of the equivalence false: a generator placed at the payload root cannot also equal the ordered pair of itself with alpha in a finite tree. Thus the theorem does not assert existence for arbitrary simultaneous placements. The locator premise is also essential: a value assigned independently of the actual generator subtree need not agree with the emitted link.

For RankedExpr k m, use the generator type Fin k plus Fin m. Locate each rank generator at the right child of its atomic-role representative and each residual generator at its own representative. Assign the rank generator T(n) and the residual its finite tree. A decoration c then emits the original link to epoch c and evaluates to T(n+c). This application additionally requires the separate atomic-feedback correspondence to establish those original generator values.

This is a native semantic compiler theorem obtained by ordinary finite structural induction; no literature-originality claim is made. It supplies the payload clause of the general acquired-fiber construction. Arbitrary-context exterior reconstruction, atomic feedback, cross-role inequalities, additional negative records, rank-only suffix refinements and explicit inverse laws remain distinct obligations. The theorem provides neither an observer-accessible equality port nor an arbitrary-policy decision procedure, resource bound or full acquired-fiber bijection.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation.payload_history_exact`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber](NativeFiveHoleFiber.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection](NativePrefixIdentityReflection.md)
