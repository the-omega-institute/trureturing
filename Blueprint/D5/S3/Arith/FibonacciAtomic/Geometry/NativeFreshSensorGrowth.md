# Native fresh sensor growth

## Abstract

Fixed original-leaf growth is a successful guarded native execution with fresh-zero rational values.

**Theorem 1.1 (Execution on every finite native source).**

$$\forall t: \operatorname{Source}\left(\right), (\operatorname{run}\left(t, \operatorname{calls}\left(t\right)\right) = \operatorname{some}\left(\operatorname{grown}\left(t\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.executes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source is the original Bool free magma, with true denoting alpha and false beta. The function grown replaces alpha by (beta,alpha) and beta by ((beta,alpha),alpha). The calls traverse the original leaves from left to right. At alpha they promote then split its owner; at beta they split its owner then its left child. Only guarded structural calls occur. Successful traces lift through the existing native runner in arbitrary output contexts.

**Theorem 1.2 (Actual execution and fresh-zero inclusion).**

$$\forall t: \operatorname{Source}\left(\right), ((\operatorname{D}\left(t\right)) \Rightarrow (\forall l: \operatorname{RawMap}\left(\right), (\forall n: \mathbb{Z}, (\forall x: \operatorname{Value}\left(\right), (\exists m: \operatorname{RawMap}\left(\right), (\exists j: \mathbb{Z}, (\exists y: \operatorname{Value}\left(\right), ((\operatorname{nativeRun}\left(t, l, n, x, \operatorname{calls}\left(t\right)\right) = \operatorname{some}\left(\operatorname{tuple}\left(\operatorname{grown}\left(t\right), m, j, y\right)\right)) \land ((\forall p: \operatorname{Address}\left(\right), ((p \in \operatorname{material}\left(t\right)) \Rightarrow (\operatorname{y}\left(p\right) = \operatorname{x}\left(p\right)))) \land (\forall p: \operatorname{Address}\left(\right), ((p \in \operatorname{material}\left(\operatorname{grown}\left(t\right)\right)) \Rightarrow ((\neg (p \in \operatorname{material}\left(t\right))) \Rightarrow (\operatorname{y}\left(p\right) = 0)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.actual_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The raw table and next integer are the actual nativeRun arguments and outputs. Every old material address keeps its original rational value and every new material address receives zero. This is the old-cell inclusion E on the same actual attained source. The installation still presumes authentic exhaustive raw bindings, current and fresh rights, complete exclusive framing, exact arithmetic, Hold and sufficient backing. Physical conformance and record isolation remain installation premises. The separate raw_bindings theorem characterizes every inherited and freshly allocated label on this same run; none of these claims acquires an installation premise.

**Theorem 1.3 (Full material, terminal and designated counts).**

$$\forall t: \operatorname{Source}\left(\right), (((\operatorname{length}\left(\operatorname{material}\left(\operatorname{grown}\left(t\right)\right)\right)) + (1) = (5 \cdot (\operatorname{fst}\left(\operatorname{composition}\left(t\right)\right))) + (7 \cdot (\operatorname{snd}\left(\operatorname{composition}\left(t\right)\right)))) \land ((\operatorname{length}\left(\operatorname{terminals}\left(\operatorname{grown}\left(t\right)\right)\right) = (2 \cdot (\operatorname{fst}\left(\operatorname{composition}\left(t\right)\right))) + (3 \cdot (\operatorname{snd}\left(\operatorname{composition}\left(t\right)\right)))) \land ((\operatorname{length}\left(\operatorname{sensors}\left(t\right)\right) = \operatorname{length}\left(\operatorname{leaves}\left(t\right)\right)) \land (\forall p: \operatorname{Address}\left(\right), ((p \in \operatorname{sensors}\left(t\right)) \Rightarrow (p \in \operatorname{terminals}\left(\operatorname{grown}\left(t\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a and c are the original composition counts, grown(t) has 5a+7c-1 actual material cells and 2a+3c current terminals. There is exactly one designated sensor per original logical leaf, and every such sensor is an actual current terminal. Counts include beta material markers and all nondesignated fresh terminals.

**Theorem 1.4 (Ambient parent cancellation for a zero root).**

$$\forall l: \operatorname{Source}\left(\right), (\forall r: \operatorname{Source}\left(\right), (\forall b: \operatorname{Bool}\left(\right), (\forall x: \operatorname{Value}\left(\right), ((\operatorname{x}\left(\operatorname{empty}\left(\right)\right) = 0) \Rightarrow (\operatorname{update}\left(\operatorname{mul}\left(l, r\right), \operatorname{lift}\left(b, x\right)\right) = \operatorname{lift}\left(b, \operatorname{update}\left(\operatorname{if}\left(b, r, l\right), x\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.update_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The update sums the native neighbors at each material address and is zero outside material. Lift prefixes one edge and assigns zero at every exterior address. The attached root must have value zero; its contribution to the external parent then vanishes. The equation covers every address, including the exterior, and uses no assumed matrix actions.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.actual_values`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.executes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.inventory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.update_lift`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair](NativeGuardedLeafRepair.md)
