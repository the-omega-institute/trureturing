# The full finite named family

## Abstract

Finite canonical native branching before free-shape unification

X is the entire declared finite family of names, represented by a presentation p. An Equation is a primitive definition z=T(n), a native shift definition z=rho to power a of x, an ordered pair definition z=pair(x,y), or an equality x=y. Every occurrence of a name refers to the same original source value. Unused declared names remain in X. Source consists of arbitrary finite ordered Boolean trees, and rho is the actual native substitution, not a free unary symbol. In the display, canonicalCodes(v)(x)=encode(v(x)), canonicalShapes(v)(x)=shape(encode(v(x))), NativeHolds is Equation.Holds, and BranchHolds is BranchEquation.Holds.

**Definition 1.1 (Executable finite constructor choices).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.branches`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.branches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

choices retains primitive, shift and equality equations. For each pair definition it offers exactly an ordinary case and a collapse case. branches forms their finite ordered product over the whole input list, retaining repeated constraints. An ordinary case requires the output code to be the pair of its input codes. A collapse case requires input ranks r+1 and r and output rank r+2 for some unrestricted natural r. That rank is not enumerated or bounded. Every code in the theorem is the actual canonical encode of the same original valuation.

**Definition 1.2 (Erase ranks only after selecting cases).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.shape`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.shape` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

shape replaces each primitive rank by one fixed free primitive leaf and preserves ordered pairs. Primitive definitions and collapse cases become primitive shape equalities. Shift definitions become equalities of shapes. An ordinary pair definition becomes a free binary constructor equation. No interpreted native power is sent to the free occurs check. The exact canonical branch equations are retained alongside these weaker free-shape equations.

**Theorem 1.3 (Exact canonical branching with total MGU shape reconstruction).**

$$\forall X: Type, (\forall p: \operatorname{Presentation}\left(X\right), (\forall E: \operatorname{List}\left(\operatorname{Equation}\left(X\right)\right), (\forall v: X \to Source, ((\forall e: \operatorname{Equation}\left(X\right), ((\operatorname{ListMem}\left(e, E\right)) \implies (\operatorname{NativeHolds}\left(v, e\right)))) \iff (\exists B: \operatorname{List}\left(\operatorname{BranchEquation}\left(X\right)\right), ((\operatorname{ListMem}\left(B, \operatorname{branches}\left(E\right)\right)) \land ((\forall x: X, (\operatorname{Normal}\left(\operatorname{encode}\left(\operatorname{v}\left(x\right)\right)\right))) \land ((\forall b: \operatorname{BranchEquation}\left(X\right), ((\operatorname{ListMem}\left(b, B\right)) \implies (\operatorname{BranchHolds}\left(\operatorname{canonicalCodes}\left(v\right), b\right)))) \land (\exists S: SubstInfo, ((\operatorname{unify}\left(\operatorname{encodeEquations}\left(p, \operatorname{shapeEquations}\left(B\right)\right), empty\right) = \operatorname{ok}\left(S\right)) \land ((\forall x: X, (\operatorname{evaluate}\left(\operatorname{canonicalShapes}\left(v\right), \operatorname{action}\left(p, S, x\right)\right) = \operatorname{shape}\left(\operatorname{encode}\left(\operatorname{v}\left(x\right)\right)\right))) \land (\forall a: \operatorname{Occurrence}\left(X\right), (\forall b: \operatorname{Occurrence}\left(X\right), ((\operatorname{ListMem}\left(a, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \implies ((\operatorname{ListMem}\left(b, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \implies ((\operatorname{Connected}\left(\operatorname{shapeEquations}\left(B\right), \operatorname{action}\left(p, S\right), a, b\right)) \iff (\operatorname{sort}\left(a\right) = \operatorname{sort}\left(b\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.native_branch_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every presentation p, finite named equation list E and entire original valuation v, all native equations hold exactly when there is a member B of the computed finite list branches(E) such that all canonical codes are normal, all exact code equations of B hold, and the actual free unifier of shapeEquations(B) succeeds. Evaluating its total action at the original canonical shapes returns the original shape at every declared name. Among its enumerated residual occurrences, connectivity is equivalent to equality of residual sort. ListMem in the display denotes ordinary list membership; sort(x,p,y) is y.

Canonical encoding commutes with every actual native power. This follows by structural induction from the commutation of smart collapse with a common rank shift. At each pair, the two canonical input codes either have consecutive primitive ranks and collapse, or smart retains the ordinary pair. This gives a complete finite case selection. Conversely, expansion of each selected code equation gives its actual native equation, including the collapse identity. Erasing ranks then supplies a ground solution of every selected free-shape equation. Existing unification completeness gives the actual successful result, its restriction identity reconstructs all named shapes, and the exact residual-occurrence graph theorem gives the connected sort components.

This is the canonical case reduction for an already named finite system. It does not construct the naming program for arbitrary MixedExpr inputs, solve affine rank equalities, compute minimum block bases, return an executable list of unrestricted native image charts, reconstruct all native outputs from independent bases, or perform signed pullback. The exact code constraints in this intermediate reduction are not a synthesized positive image cover.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.branches`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.native_branch_reduction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.shape`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFiniteNormalInversion](NativeFiniteNormalInversion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover](NativePositiveImageCover.md)
