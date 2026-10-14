# Whole guarded five-hole fibers and complete labels

## Abstract

NativeFiveHoleFiber

**Definition 1.1 (The complete guarded raw record).**

$$\forall u: Source, ((\operatorname{Raw}\left(u\right)) \iff ((\operatorname{literalRecord}\left(\operatorname{singleton}\left(\operatorname{nil}\left(\right)\right), u\right) = \operatorname{rootLabel}\left(\right)) \land ((\operatorname{readout}\left(\operatorname{nil}\left(\right), u\right) = \operatorname{branch}\left(\right)) \land ((\operatorname{readout}\left(\operatorname{R}\left(\right), u\right) = \operatorname{branch}\left(\right)) \land ((\operatorname{readout}\left(\operatorname{RR}\left(\right), u\right) = \operatorname{branch}\left(\right)) \land ((\operatorname{readout}\left(\operatorname{RRR}\left(\right), u\right) = \operatorname{branch}\left(\right)) \land ((\operatorname{readout}\left(\operatorname{RRRLL}\left(\right), u\right) = \operatorname{alpha}\left(\right)) \land ((\operatorname{readout}\left(\operatorname{RRRRL}\left(\right), u\right) = \operatorname{alpha}\left(\right)) \land ((\operatorname{GuardedEqual}\left(0, \operatorname{RRRLR}\left(\right), 1, \operatorname{RL}\left(\right), u\right)) \land (\operatorname{GuardedEqual}\left(0, \operatorname{RRRRR}\left(\right), 1, \operatorname{RRL}\left(\right), u\right)))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.Raw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source is the finite free magma on the two native leaves. Addresses are Boolean words, false for L and true for R. F(y) pairs alpha with the actual substitution of y. V(x,y,z) pairs x with the successive holes y, z, F(y), F(z). Q consists of L, RL, RRL, RRRL and RRRR.

RootLabel is the complete one-hole row at the empty address. GuardedEqual requires presence at both supplied endpoints and equality of the entire transformed subtrees. All original literals and both positive copies concern the same finite source.

**Theorem 1.2 (The complete root row is constant).**

$$\forall u: Source, (\operatorname{literalRecord}\left(\operatorname{singleton}\left(\operatorname{nil}\left(\right)\right), u\right) = \operatorname{rootLabel}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.root_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty finite source is hidden by the root hole. Its literal exterior is the empty-address hole and its complete partition has one class. This equality keeps the entire row, including the partition, rather than only a point reply.

**Theorem 1.3 (Every raw source has the full source shape).**

$$\forall u: Source, ((\operatorname{Raw}\left(u\right)) \iff (\exists x, y, z: Source, (u = \operatorname{V}\left(x, y, z\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.raw_fiber_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four branch replies extract the full outer skeleton. The alpha replies force branches in its last two holes. Transport at epoch one and the guarded copies identify their right children with the substitutions of y and z. Conversely every source of this shape satisfies the root row, every literal, both endpoint guards and both copied equalities. The parameterization covers the entire raw fiber.

**Theorem 1.4 (All cut endpoints remain reached at every epoch).**

$$\forall a: Nat, (\forall x, y, z: Source, (\forall i: \operatorname{Fin}\left(5\right), (\operatorname{subtree}\left(\operatorname{position}\left(i\right), \operatorname{iterate}\left(\operatorname{substitution}\left(\right), a, \operatorname{V}\left(x, y, z\right)\right)\right) = \operatorname{some}\left(\operatorname{iterate}\left(\operatorname{substitution}\left(\right), a, \operatorname{hole}\left(x, y, z, i\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.epoch_hole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original present transport applies at each already reached cut address. Arbitrary supplied natural epochs retain both guards of every negative record. The comparison is between entire transformed holes.

**Definition 1.5 (All six class comparisons).**

$$\forall y, z: Source, ((\operatorname{Distinct}\left(y, z\right)) \iff ((y \neq z) \land ((y \neq \operatorname{F}\left(y\right)) \land ((y \neq \operatorname{F}\left(z\right)) \land ((z \neq \operatorname{F}\left(y\right)) \land ((z \neq \operatorname{F}\left(z\right)) \land (\operatorname{F}\left(y\right) \neq \operatorname{F}\left(z\right))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.Distinct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both labels contain the same complete four-branch exterior. The false label has partition blocks {L,RL}, {RRL}, {RRRL}, {RRRR}. The true label has blocks {L,RRRL}, {RL}, {RRL}, {RRRR}. Label compares every ordered pair in Q, including reflexive and reversed pairs.

**Theorem 1.6 (The entire exterior and partition determine the parameters).**

$$\forall s: Bool, (\forall x, y, z: Source, ((\operatorname{literalRecord}\left(\operatorname{Q}\left(\right), \operatorname{V}\left(x, y, z\right)\right) = \operatorname{label}\left(s\right)) \iff ((x = \operatorname{ite}\left(s, \operatorname{F}\left(y\right), y\right)) \land (\operatorname{Distinct}\left(y, z\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.complete_label_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward direction extracts the repeated block and all six inequalities from the complete partition. The reverse checks every pair of holes and the whole exterior. No chosen representative narrows the fiber.

**Theorem 1.7 (Exact membership in each original whole stratum).**

$$\forall s: Bool, (\forall H: History, (\forall u: Source, ((\operatorname{Stratum}\left(s, H, u\right)) \iff (\exists y, z: Source, ((u = \operatorname{source}\left(s, y, z\right)) \land ((\operatorname{Distinct}\left(y, z\right)) \land (\operatorname{Protected}\left(H, \operatorname{source}\left(s, y, z\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.raw_stratum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

History is any finite list of negative records between Q endpoints, at arbitrary supplied natural epochs. Supported constrains only endpoints. IndexedHistory reconstructs the original list exactly, retaining order and repetitions. Negative contains both guards and the whole-subtree disequality. Protected conjoins every original occurrence. D is Raw intersected with Protected; Stratum additionally fixes the full literal record. Other labels of D remain part of D.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.Distinct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.Raw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.complete_label_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.epoch_hole`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.raw_fiber_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.raw_stratum_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.root_record`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
