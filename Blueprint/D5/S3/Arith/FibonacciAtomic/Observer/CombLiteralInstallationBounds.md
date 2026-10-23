# Literal installation and actual Read lower bounds

## Abstract

CombLiteralInstallationBounds

A source is a nonempty full ordered Boolean tree. Source true is alpha and contributes zero to original parity; source false is beta and contributes one. Addresses use false for left and true for right. A controller has one common initial control and a source-free instruction function. Each Read row fixes its literal address and branches on exactly one of alpha, beta, branch or absent. A genuine Update substitutes the actual source and advances its epoch. Internal steps receive no source information; each Halt row has one fixed Boolean output.

Correct(M,h,T) requires sourcewise termination and original-parity correctness for every h-leaf source and every entry t at most T. Source shape, labels and entry are not control inputs. Run(M,u,e,t,qs,updates,f,b) records a first-halt execution from control e at epoch t; qs records actual Read occurrences with their epochs, and updates counts genuine Updates. These records are proof annotations, not additional mutable storage. Static(M,h,T) says every promised successful run has zero actual Updates; unreachable Update rows are allowed.

Queries and halts filter the entire finite control type, including unreachable installed rows. All mutable control is counted. The bounds allow unrestricted changes of control, so they apply in particular when each immediate change is restricted to hold or one bit. The proof is symbolic for arbitrary finite sizes, not a finite enumeration or a certified individual controller.

**Theorem 1.1 (Every successful run reads every original leaf).**

$$\forall E: Type, (\forall M: \operatorname{Controller}\left(E\right), (\forall h, T: Nat, ((\operatorname{Correct}\left(M, h, T\right)) \implies (\forall u: Source, ((\operatorname{length}\left(u\right) = h) \implies (\forall t: Nat, ((t \leq T) \implies (\forall qs: \operatorname{List}\left(E \times Nat\right), (\forall updates: Nat, (\forall f: E, (\forall b: Bool, ((\operatorname{Run}\left(M, u, \operatorname{initial}\left(M\right), t, qs, updates, f, b\right)) \implies (h \leq \operatorname{length}\left(qs\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.successful_run_read_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each original leaf, flipping just that leaf preserves the original length and changes parity. Until a separating Read the same controller follows the same run on the two sources, including genuine Updates. Such a Read must lie inside that original leaf cone. Distinct original leaf cones are disjoint, giving an injection from original leaves into Read occurrences on this particular run. No finite-control assumption is needed.

**Theorem 1.2 (Complete installed union over all comb shapes).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)] \forall M: \operatorname{Controller}\left(E\right), (\forall h, T: Nat, ((0 < h) \implies ((\operatorname{Correct}\left(M, h, T\right)) \implies ((2^{h - 1} \leq \operatorname{card}\left(\operatorname{queries}\left(M\right)\right)) \land (2 \leq \operatorname{card}\left(\operatorname{halts}\left(M\right)\right)) \land ((2^{h - 1}) + 2 \leq \operatorname{card}\left(E\right)) \land (\forall width: Nat, (\forall encode: E \to \{w: \operatorname{Fin}\left(width\right) \to Bool \mid \operatorname{Adm}\left(width, w\right)\}, ((\operatorname{Injective}\left(encode\right)) \implies ((2^{h - 1}) + 2 \leq \operatorname{fib}\left((width) + 2\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.comb_installed_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every address of length h minus one, the comb with that tip has exactly h leaves, including the empty tip at h=1. Opposite tip labels force an installed Read in that tip cone. Equal-depth tip cones are disjoint, giving the exponential query count across the entire family of shapes. Both parity outputs occur, requiring two distinct Halt rows disjoint from queries. The admissible no-11 word count is fib(width+2), so any injective encoding of the entire control type has the displayed Fibonacci capacity. This installed-union bound does not assert exponentially many Reads on one run.

**Theorem 1.3 (Static installed union over all entries).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)] \forall M: \operatorname{Controller}\left(E\right), (\forall h, T: Nat, ((0 < h) \implies ((\operatorname{Correct}\left(M, h, T\right)) \implies ((\operatorname{Static}\left(M, h, T\right)) \implies (((2^{h - 1}) \times (\operatorname{div}\left((T) + 3, 3\right)) \leq \operatorname{card}\left(\operatorname{queries}\left(M\right)\right)) \land (2 \leq \operatorname{card}\left(\operatorname{halts}\left(M\right)\right)) \land (((2^{h - 1}) \times (\operatorname{div}\left((T) + 3, 3\right))) + 2 \leq \operatorname{card}\left(E\right)) \land (\forall width: Nat, (\forall encode: E \to \{w: \operatorname{Fin}\left(width\right) \to Bool \mid \operatorname{Adm}\left(width, w\right)\}, ((\operatorname{Injective}\left(encode\right)) \implies (((2^{h - 1}) \times (\operatorname{div}\left((T) + 3, 3\right))) + 2 \leq \operatorname{fib}\left((width) + 2\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.static_comb_installed_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each tip, a static controller must distinguish the adjacent atomic sources at every entry from zero through T. A separating suffix lies in a three-entry interval determined by its weighted depth, with left cost one and right cost two. An injection from entries to installed query rows paired with three slots yields the factor (T+3)/3, equal to the ceiling of (T+1)/3. Summing over disjoint tip cones gives the product bound. Natural division is used. The Fibonacci inequalities hold for every actual correct installation, hence also for a minimizing installation when one exists; neither existence nor attainment of a minimum is asserted here. In particular the conclusions include the positive regimes T=0 or even h without adding that restriction to these necessary bounds.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.comb_installed_lower_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.static_comb_installed_lower_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.successful_run_read_lower_bound`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine](NativeSerialMachine.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](../SourceTransportCentralizer.md)
