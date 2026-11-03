# Finite Presburger construction for original canonical image filters

## Abstract

NativeEffectiveImageGuard

**Theorem 1.1 (Exact simultaneous acceptance for a guarded system).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{Input}\left(n, k, m\right), (\forall guarded: \operatorname{Guarded}\left(\operatorname{equations}\left(I\right)\right), (\forall mode: \operatorname{Mode}\left(\operatorname{threshold}\left(\operatorname{filters}\left(I\right)\right), m\right), (\forall p: \operatorname{Fin}\left(n\right) \to Nat, ((\operatorname{holds}\left(\operatorname{imageGuard}\left(I, mode\right), \operatorname{environment}\left(p\right)\right)) \iff ((\operatorname{Legal}\left(I, p\right)) \land (\operatorname{Passes}\left(\operatorname{ranks}\left(I, p\right), \operatorname{canonical}\left(\operatorname{equations}\left(I\right), \operatorname{ranks}\left(I, p\right), guarded, mode\right), \operatorname{filters}\left(I\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard.effective_image_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input I has one original finite tuple of natural parameters p. Each finite token index is an integer affine expression in that tuple, with its explicit nonnegativity guard. The original Presburger guard and every index guard are conjuncts of the constructed formula. The same derived rank map is used throughout the equations and all filter occurrences. Every original expression, offset, ground, ordered pair and repeated filter remains present.

For a pair-guarded optional-definition system, a mode fixes each undefined state to one exceptional atom or assigns Omega. Its canonical extension is taken in the full native completion. The finite formula imageGuard is true exactly when the original parameter is legal and every original filter value on that same canonical extension belongs to its actual native image. The completion and the outputs have no finiteness or rationality restriction.

Atomic terminal alternatives are supplied by atomicGuard, whose recursion decreases the requested target rank. A finite ground uses its finite native parse, retaining both atomic terminal alternatives and ordered pair closure. A finite parameter token T(q(p)+c) belongs to image t exactly when q(p)+c is at least t. Omega belongs to every image. For a decorated state rho(a)Y, a at least t makes the obligation true; otherwise it refers to the same state at threshold t-a.

Set s to the maximum original filter threshold, including zero. There are finitely many state and threshold keys, with thresholds from zero through s. The pinned finite Cartesian-product list program enumerates all Boolean labelings of these keys. For each labeling the formula requires every selected state key to satisfy its finite positive defining clause, then requires all original filter expressions to pass under that same labeling. The disjunction over these finite labelings is a finite Presburger formula. This enumerates finite graph labels and does not enumerate parameter values or introduce independent ranks.

For completeness, label each key by its actual image membership in the one canonical completed tuple. The exact native image decomposition satisfies every selected clause and every passing root expression. For soundness, a selected zero-decorated state unfolds its defining equation; a positive decorator either passes directly or reduces the threshold. Pair clauses retain both exact atomic exceptions and both child obligations. These obligations, together with already known image members, form a post-fixed relation for the completed image grammar. The existing native image corecursor supplies actual preimages for this relation. Thus arbitrary cycles are accepted precisely through greatest-fixed-point semantics, with no finite-prefix surrogate.

All empty cases are included: an empty filter conjunction is true, a system may have no states or parameter atoms, and threshold zero is the whole completion. The construction asserts total finite syntax and exact semantics; it makes no polynomial bound or whole acquired-input synthesis claim.

**Theorem 1.2 (Effective original-system acceptance with all reconstructed names).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{Input}\left(n, k, m\right), (\forall mode: \operatorname{EffectiveMode}\left(I\right), (\forall p: \operatorname{Fin}\left(n\right) \to Nat, (((\operatorname{holds}\left(\operatorname{originalImageGuard}\left(I, mode\right), \operatorname{environment}\left(p\right)\right)) \iff ((\operatorname{Legal}\left(I, p\right)) \land (\operatorname{SourcePasses}\left(I, p, \operatorname{effectiveCanonical}\left(I, mode, p\right)\right)))) \land ((\operatorname{holds}\left(\operatorname{originalImageGuard}\left(I, mode\right), \operatorname{environment}\left(p\right)\right)) \iff ((\operatorname{Legal}\left(I, p\right)) \land (\exists v: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\operatorname{SourceSatisfies}\left(I, p, v\right)) \land ((\operatorname{EffectiveInMode}\left(I, mode, p, v\right)) \land (\operatorname{SourcePasses}\left(I, p, v\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard.original_effective_image_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An original system may contain arbitrary decorated root links. The program effectiveNormalForm inspects the original finite state list in order and selects the first syntactic root link. A self-link of weight zero becomes free; a positive self-link becomes Omega. A link to a different state is eliminated by the existing simultaneous substitution and inert-slot step. Both original expression maps are composed after every step. The strict decrease in the number of root links proves that the original number of states is sufficient fuel. Every step is the previously established exact two-way transformation of the entire completed solution relation.

The normalized input keeps the original affine index list and original guard. Every filter occurrence is substituted through its original reconstruction, with its threshold and multiplicity retained. EffectiveMode chooses fixed or live alternatives exactly on the undefined states of this computed presentation. effectiveTotalMode adds inert entries at the defined names. EffectiveInMode reads that mode on the exact projected original valuation. The original canonical tuple effectiveCanonical reconstructs every original name from the one canonical normalized extension.

The formula originalImageGuard first executes this finite syntactic normalization and then the finite guarded image construction. Its first equivalence states exact acceptance of every original filter on effectiveCanonical, together with the original Legal guard. Its second equivalence states existence of one entire original completed assignment satisfying all original equations, this same projected mode and all original filters, again at the same legal parameter tuple. The forward and reverse projection maps and finite-exception completeness establish the second equivalence.

This gives the effective parameter acceptance assertion of Proposition 4.3 using a completely specified syntactic normalization. The canonical completed values themselves may be defined semantically by their unique guarded extension; the computed formula contains no semantic choice. All original completed values remain available to the existence quantifier, including non-rational ones. The result concerns functional systems and their retained image filters; the separate whole acquired-input synthesis and effective-prefix assertions require their own hypotheses and conclusions.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard.effective_image_guard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard.original_effective_image_guard`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard](NativeEffectiveAtomicGuard.md)
