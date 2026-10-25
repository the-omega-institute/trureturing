# Canonical finite coordinates and executable native prefixes

## Abstract

OriginalCanonicalClassification

**Theorem 1.1 (Exact canonical classification, finite rigidity and inclusive prefixes).**

$$\forall k: Nat, (\forall m: Nat, (\forall E: \operatorname{Definitions}\left(k, m\right), (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), ((\operatorname{Solution}\left(E, mode, p, \operatorname{canonical}\left(E, mode, p\right)\right)) \land (\forall e: \operatorname{Expr}\left(k, m\right), ((\operatorname{isSome}\left(\operatorname{canonicalCompile}\left(E, mode, e\right)\right) = true) \iff (\operatorname{IsFinite}\left(\operatorname{value}\left(mode, p, \operatorname{canonical}\left(E, mode, p\right), e\right)\right)))) \land (\forall e: \operatorname{Expr}\left(k, m\right), (\forall f: \operatorname{FiniteExpr}\left(k\right), ((\operatorname{canonicalCompile}\left(E, mode, e\right) = \operatorname{some}\left(f\right)) \implies (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(E, mode, p, v\right)) \implies (\operatorname{value}\left(mode, p, v, e\right) = \operatorname{embed}\left(\operatorname{finiteValue}\left(p, f\right)\right))))))) \land (\forall e: \operatorname{Expr}\left(k, m\right), ((\operatorname{canonicalCompile}\left(E, mode, e\right) = none) \implies (\neg(\operatorname{IsFinite}\left(\operatorname{value}\left(mode, p, \operatorname{canonical}\left(E, mode, p\right), e\right)\right))))) \land (\forall h: Nat, (\forall e: \operatorname{Expr}\left(k, m\right), (\forall a: Address, ((\operatorname{length}\left(a\right) \le h) \implies (\operatorname{prefixReply}\left(E, mode, p, h, e, a\right) = \operatorname{completionReadout}\left(a, \operatorname{value}\left(mode, p, \operatorname{canonical}\left(E, mode, p\right), e\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalCanonicalClassification.original_canonical_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E assign at most one defining expression to each of m states. Expressions contain finite grounds, original parameter atoms, literal Omega, fixed nonnegative powers of states, and ordered pairs. A mode fixes which parameter atoms are finite. The vector p retains every original natural parameter, including unused names and distinct names with equal values. The result holds for every p, and hence for every p satisfying an accepted arithmetic guard.

Normalization computes the least remaining root link and applies its native substitution. A zero self-link becomes a free alias; a positive self-link forces Omega. Each step strictly decreases the finite set of root links. The resulting syntax and reconstruction are computed without inspecting any parameter value. Reconstruction maps every normalized solution to an original solution and fixes every original solution exactly.

The canonical vector reconstructs the actual native solution with Omega at all undefined normalized states. This is the existing unrestricted CompletionTree interpretation of rho, ordered pairing and finite embedding. Arbitrary completed free assignments still give solutions, and the normalized solution is unique conditional on those assignments.

The finite compiler examines only normalized displayed syntax, using at most the number of states in its saturation. Its successful outputs are finite expressions in grounds, original parameter atoms, fixed powers and pairs. Success is equivalent to actual canonical finiteness for every original expression. Every solution has the compiled finite value. Failure proves that the canonical value is infinite; another assignment to a free state may give a finite value.

Completeness uses a finite native witness. An ordered pair leaves a nonempty sibling, so recursive calls descend in finite leaf count. Native power reflection preserves finiteness, and the exact Fibonacci length formula bounds the preimage leaf count by the image leaf count. Undefined canonical states and literal Omega have no finite witness. This produces a finite syntactic derivation, which the finite compiler resolves. Atomic coincidences and pairs that become atomic do not alter the argument.

The executable prefix procedure uses finite trees only. At stage n it fills each Omega terminal by a complete finite binary tree through depth n minus one, evaluates finite terminals at the supplied parameters, and performs n guarded iterations. The stage-n vector agrees with the native canonical vector at every address of length less than n. Actual rho powers preserve that agreement and each ordered pair gains one depth.

For the inclusive bound h, prefixTree uses stage h plus one and evaluates the entire original reconstruction. prefixReply then reads the requested finite address. The last conjunct covers all addresses of length at most h, including h equal to zero and absent descendants of early leaves. Alpha, beta, branch and absence retain their literal native meanings. The procedure does not evaluate an infinite semantic tree and uses no supplied rank, normalization oracle, semantic finiteness test or bound on p.

For any FunctionalCase, apply the statement to its unchanged definitions and mode, then take e to be each designated original reconstruction expression. Zero state and parameter counts retain their literal empty-function meanings. Chart extraction and recognition of the accepted functional orientation are separate questions. No external novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalCanonicalClassification.original_canonical_synthesis`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion](../CompletionPositiveDriftRegion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction](OriginalNativeConstruction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap](../../SourceCoordinates/NativeRotationDepthGap.md)
