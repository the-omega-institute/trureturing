# Native completed solutions of functional cases

## Abstract

OriginalNativeConstruction

**Theorem 1.1 (The native corecursor satisfies every simultaneous equation).**

$$\forall k: Nat, (\forall m: Nat, (\forall E: \operatorname{Definitions}\left(k, m\right), ((\operatorname{PairGuarded}\left(E\right)) \implies (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall g: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(E, mode, p, \operatorname{native}\left(E, mode, p, g\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((E\left(i\right) = none) \implies (\operatorname{native}\left(E, mode, p, g\right)\left(i\right) = g\left(i\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formulas, Function(A,B) denotes functions from A to B. For a system with no variable at a defining root, the constructed native vector satisfies every definition and agrees exactly with the supplied completed assignment at every undefined state. Constants and literal Omega are permitted defining roots; recursive state occurrences are below pairs. The root-link normalization theorem derives this shape from the original functional system.

**Theorem 1.2 (Uniqueness conditional on all free values).**

$$\forall k: Nat, (\forall m: Nat, (\forall E: \operatorname{Definitions}\left(k, m\right), ((\operatorname{PairGuarded}\left(E\right)) \implies (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall g: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), (((\operatorname{Solution}\left(E, mode, p, v\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((E\left(i\right) = none) \implies (v\left(i\right) = g\left(i\right))))) \implies (v = \operatorname{native}\left(E, mode, p, g\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every native solution with the given free assignment equals the constructed vector. Expression evaluation is a coalgebra morphism: the source equations justify each defined root, the free assignment justifies every undefined root, and ordered-pair children retain the same expression valuation. Final-coalgebra uniqueness then applies to this concrete native morphism.

**Theorem 1.3 (Simultaneous construction, conditional uniqueness and exact reconstruction).**

$$\forall k: Nat, (\forall m: Nat, (\forall E: \operatorname{Definitions}\left(k, m\right), (\exists N: \operatorname{Definitions}\left(k, m\right), (\exists R: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), \operatorname{Expr}\left(k, m\right)\right), ((\operatorname{PairGuarded}\left(N\right)) \land (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), ((\forall g: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), (\operatorname{Solution}\left(E, mode, p, \operatorname{reconstruct}\left(mode, p, R, \operatorname{native}\left(N, mode, p, g\right)\right)\right))) \land (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(E, mode, p, v\right)) \implies ((\operatorname{Solution}\left(N, mode, p, v\right)) \land (\operatorname{reconstruct}\left(mode, p, R, v\right) = v) \land (\operatorname{reconstruct}\left(mode, p, R, \operatorname{native}\left(N, mode, p, v\right)\right) = v)))) \land (\forall g: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), (\forall u: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(N, mode, p, u\right)) \implies ((\forall i: \operatorname{Fin}\left(m\right), ((N\left(i\right) = none) \implies (u\left(i\right) = g\left(i\right)))) \implies (u = \operatorname{native}\left(N, mode, p, g\right)))))) \land (\forall g: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(N, mode, p, \operatorname{native}\left(N, mode, p, g\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((N\left(i\right) = none) \implies (\operatorname{native}\left(N, mode, p, g\right)\left(i\right) = g\left(i\right)))))) \land (\forall e: \operatorname{Expr}\left(k, m\right), (\forall f: \operatorname{FiniteExpr}\left(k\right), ((\operatorname{finiteCompile}\left(E, mode, e\right) = \operatorname{some}\left(f\right)) \implies (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(E, mode, p, v\right)) \implies (\operatorname{value}\left(mode, p, v, e\right) = \operatorname{embed}\left(\operatorname{finiteValue}\left(p, f\right)\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.original_native_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is any finite functional system in the literal-Omega source syntax. Normalization and its reconstruction are obtained from that system and do not depend on parameters. There is no assumed normalized presentation or supplied solution. The conclusions hold for all natural parameter values and therefore for every value satisfying the retained arithmetic guard.

The function native is an actual corecursor into the existing unrestricted CompletionTree. Its states are displayed expressions or native trees being copied. A defined pair emits an ordered native branch immediately. Fixed powers distribute over that branch using the actual substitution rho. Finite grounds, parameter atoms, literal Omega and arbitrary completed free assignments use their actual native values. The proof establishes composition with fixed powers and expression evaluation before deriving the simultaneous equations.

For each assignment to undefined normalized states, native satisfies the normalized equations and has exactly those free values. It is the unique normalized solution with that assignment, by the instantiated final-coalgebra morphism law. Reconstructing it gives an original solution. Every original solution restricts to a normalized solution and is recovered by the same construction with its own free values. Erased state names may remain as unused normalized coordinates; their supplied values do not create additional original choices.

Assigning the actual Omega to every normalized free coordinate selects a canonical original solution. Applying the retained reconstruction to each original residual preserves its full native value. All state and parameter counts, bare links, zero alias cycles and positive root cycles remain in scope. This canonical selection is a semantic construction; effective prefix computation and a complete semantic finiteness classifier require additional conclusions.

The finite compiler is reused through a total internal encoding. Original parameter indices are shifted injectively, while one fixed divergent slot represents literal Omega, including at zero original parameters. This slot is representation data and is always interpreted divergently; its natural placeholder is fixed to zero. Decoding finite outputs removes it and returns expressions using only original grounds, parameters, powers and pairs. Every successful compilation is forced in every original solution, including the constructed one. Failure of this finite test is not asserted to imply canonical infinity.

The mathematical inputs are native root-link normalization, the existing finite-resolution theorem, the native substitution identities and the pinned polynomial-functor final coalgebra. No free unary substitution, bare-drift contraction, bounded rank, satisfiability assumption or supplied fixed point is used. No external novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_solution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.native_unique`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalNativeConstruction.original_native_construction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution](OriginalFiniteResolution.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFunctionalNormalization](OriginalFunctionalNormalization.md)
