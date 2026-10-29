# Sort-sensitive symbolic row exterior elimination

## Abstract

The row producer inverts a symbolic exterior against an arbitrary concrete exterior while retaining every address hole and every repeated variable binding. It is the exact structural child needed before compiling complete row equalities and disequalities into the existing native solution space.

**Theorem 1.1 (A symbolic exterior matches exactly when its finite bindings hold).**

$$\forall X:Type,\ \forall p:\operatorname{SymbolicExterior}(X),\ \forall u:\operatorname{HoleExterior},\ \forall v:X\to Source,\ ((\operatorname{exteriorFill}(v,p)=u)\iff\exists bs:\operatorname{List}(X\times\operatorname{Term}(X)),\ ((\operatorname{matchExterior}(p,u)=\operatorname{some}(bs))\land\operatorname{bindingHolds}(v,bs)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination.exterior_match_exact` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matcher descends through ordered pair constructors. Boolean leaves must agree exactly, literal address holes must agree exactly, and a residual variable can match only a target subtree with no address holes. Such a subtree is decoded into a source term and recorded as a binding. The recursive list concatenation keeps repeated and shared variables visible to the later joint unifier.

The equivalence covers constructor mismatches, malformed or absent addresses, empty and repeated binding lists, and arbitrary concrete exteriors. It removes only the positive structural exterior equation; interpreted positive history equations, full row partition compilation and the NIS5.4 chart remain open.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination.exterior_match_exact`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting](../../../../../../Observer/NativeSymbolicRecutting.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace](../../../../../../Observer/NativeGroundSolutionSpace.md)
