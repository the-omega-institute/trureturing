# Native prefix identity reflection

## Abstract

NativePrefixIdentityReflection

**Theorem 1.1 (Native mass is invariant under every iterate).**

$$\forall a: Nat, (\forall t: Source, (\operatorname{gamma}\left(\operatorname{iterate}\left(substitution, a, t\right)\right) = \operatorname{gamma}\left(t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mass counts non-atomic constructors. Iterating the interpreted native substitution preserves it, including zero-mass atoms of unbounded rank.

**Theorem 1.2 (A positive child prevents atomic collapse).**

$$\forall s, t: Source, (((0 < \operatorname{gamma}\left(s\right)) \lor (0 < \operatorname{gamma}\left(t\right))) \implies (\operatorname{gamma}\left(\operatorname{mul}\left(s, t\right)\right) = 1 + \operatorname{gamma}\left(s\right) + \operatorname{gamma}\left(t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If either child has positive native mass, the parent has one plus the two child masses. No unrestricted additivity is asserted for pairs of atomic children.

**Theorem 1.3 (Native mass does not decrease toward the root).**

$$\forall s, t: Source, ((\operatorname{gamma}\left(s\right) \leq \operatorname{gamma}\left(\operatorname{mul}\left(s, t\right)\right)) \land (\operatorname{gamma}\left(t\right) \leq \operatorname{gamma}\left(\operatorname{mul}\left(s, t\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each child mass is at most the parent mass, including pairs whose two children have zero mass.

**Theorem 1.4 (The native clock advances by the iterate exponent).**

$$\forall a: Nat, (\forall t: Source, (\operatorname{kappa}\left(\operatorname{iterate}\left(substitution, a, t\right)\right) = \operatorname{kappa}\left(t\right) + a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.kappa_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The clock is zero at alpha, one at beta and two plus the right child clock at a pair. Each native substitution advances it by one.

**Theorem 1.5 (Existing finite combs realize every mass).**

$$\forall r: Nat, (\operatorname{gamma}\left(\operatorname{comb}\left(r\right)\right) = r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_comb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The comb starts at alpha and repeatedly pairs the preceding comb with alpha on the right. Its native constructor mass is exactly the number of pair steps.

**Theorem 1.6 (Closed expressions ignore residual valuations).**

$$\forall I: Type, (\forall E: \operatorname{MixedExpr}\left(I\right), ((\operatorname{active}\left(E\right) = \operatorname{false}\left(\right)) \implies (\forall z, v: I \to Source, (\operatorname{eval}\left(z, E\right) = \operatorname{eval}\left(v, E\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.eval_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An expression whose active flag is false has no live residual occurrence. Its evaluated native tree is the same under every two source valuations, without imposing any bound on ground size.

**Theorem 1.7 (Equality on a live prefix cylinder reflects globally).**

$$\forall m: Nat, (\forall d: \operatorname{Fin}\left(m\right) \to Nat, (\forall p: (i: \operatorname{Fin}\left(m\right)) \to \operatorname{Pattern}\left(\operatorname{d}\left(i\right)\right), ((\forall i: \operatorname{Fin}\left(m\right), (\operatorname{Nonempty}\left(\operatorname{Frontier}\left(\operatorname{p}\left(i\right)\right)\right))) \implies (\forall A, B: \operatorname{MixedExpr}\left(\operatorname{Fin}\left(m\right)\right), ((\forall w: (i: \operatorname{Fin}\left(m\right)) \to \operatorname{Frontier}\left(\operatorname{p}\left(i\right)\right) \to Source, (\operatorname{eval}\left((\lambda (i: \operatorname{Fin}\left(m\right)), \operatorname{fill}\left(\operatorname{p}\left(i\right), \operatorname{w}\left(i\right)\right)), A\right) = \operatorname{eval}\left((\lambda (i: \operatorname{Fin}\left(m\right)), \operatorname{fill}\left(\operatorname{p}\left(i\right), \operatorname{w}\left(i\right)\right)), B\right))) \implies (\forall z: \operatorname{Fin}\left(m\right) \to Source, (\operatorname{eval}\left(z, A\right) = \operatorname{eval}\left(z, B\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.prefix_identity_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native source algebra consists of all nonempty finite ordered binary trees with leaf labels alpha and beta. Native substitution sends alpha to beta, beta to the ordered pair (beta, alpha), and distributes through pairs. It is a fixed interpreted operation; its powers are not extra free constructors.

A mixed expression contains finite ground trees, a fixed nonnegative substitution power of an original residual name, and ordered pairing. The same name always denotes the same whole source valuation, including when its occurrences carry different fixed powers. Fixed scalar atoms and fixed barrier coordinates are evaluated into grounds before the implication is applied.

Each original coordinate has its own finite depth and pattern. A zero-depth pattern is one hole. An early observed leaf remains that leaf and contributes no descendant holes; an observed pair retains two ordered child patterns. Frontier names therefore describe exactly the reached positions, with distinct coordinates carrying disjoint private families. Every hole may receive any finite native source, independently of every other hole.

NativeDepthPatterns.depthEquiv reconstructs every finite source from its pattern and reached subtrees. NativeDepthPatterns.frontier_geometry identifies exactly the reached depth positions and recovers every assigned subtree. Relating the supplied patterns to prescribed inclusive prefixes of actual infinite completion trees requires a separate completion-tree correspondence. Inclusive observation through depth h calls for a pattern at depth h+1. The finite-tree decomposition by itself does not provide that correspondence. Early leaves preserve their absent descendants, so the reconstruction does not replace absent regions with variables.

The implication fixes all patterns and both expressions first. Its premise quantifies over the entire joint dependent product of hole fillings. Its conclusion quantifies over the entire original finite residual product. There is no feasibility assumption, chosen solution, source-size bound, common mass, common clock, or positive restriction on the concluding valuations. Zero residual dimension is included and reduces the comparison to fixed grounds.

The proof recognizes the native Fibonacci atomic subtrees by a recursive optional rank. Their constructor mass is zero; an unrecognized pair has mass one plus its child masses. A pair of recognized consecutive atoms can collapse to a single higher atom, so unrestricted constructor additivity would be false. Substitution shifts the recognized rank by one and preserves this mass. Whenever a child has positive mass, atomic collapse is excluded and pair mass is exactly additive. Finite left combs realize every nonnegative mass.

For positive hole masses, a context has an exact constant offset plus the sum of its hole masses. The offset includes the masses of maximal closed subtrees and every pair ancestor of a hole. Closed child contexts can collapse atomically; live child contexts have a positive descendant and make their ancestors additive. The induction includes pairs with one empty child frontier and patterns with no frontier.

An expression has an exact ground-and-constructor offset plus its residual occurrence counts times the context masses. Counts retain repetitions and ignore only the fixed decorations, whose mass is invariant. Testing mass one at all holes and then increasing one selected named hole to mass two isolates that original coordinate's coefficient. Thus a cylinder equality forces equal occurrence counts and equal offsets. A residual-containing pair has strictly positive offset and cannot equal a single decorated residual on the entire cylinder.

For two decorated occurrences of the same original name, the native right-spine clock is zero on alpha, one on beta, and two plus the right child clock on a pair. Substitution increases it by one, so equality forces equal fixed exponents by natural-number cancellation. Different names have different independent mass coefficients. Ordered-pair injection gives the two child cylinder equalities, and structural induction reflects both child identities. Residual-free expressions are independent of the valuation, including ground-versus-pair comparisons.

This is the identity-reflection clause used in Signed Local Prefix Lifting, Lemma 2.1, displayed SLP.11, and Functional Joint Contact, Theorem 4.2. By contraposition, a global nonidentity remains a nonidentity after independent live-prefix substitution. Producing one filling that breaks a whole finite list of equalities simultaneously additionally requires the distinct uniform residual separation theorem: separate witnesses for separate negatives do not supply a common witness.

A coordinate with no reached frontier can be fixed by its isolating leaf prefix, and is outside the live hypothesis. Coupling two original coordinates by requiring their hole values to agree is outside the independent product premise. Neither boundary is repaired by giving repeated occurrences fresh names.

These are mathematical coordinates and exact whole-tree equalities. Applying the result to an acquired register still requires the common source-total producer, authentic epoch, complete accessible retained-state cut and full signed source fiber. It supplies no source-selection or subtree-equality port. Acquisition, four-valued arbitrary-word reads, legal serial forward updates, literal lengths, local work, memory, retention, preparation, installation and physical time remain separately paid resources. No approximation, probability guarantee or physical cost optimum follows from the implication.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.eval_closed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_comb`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_iterate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_pair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.gamma_parent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.kappa_iterate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.prefix_identity_reflection`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
