# Exact native raw destinations

## Abstract

Every inherited and allocated raw label follows the actual guarded native run.

**Theorem 1.1 (All integer bindings of the same successful execution).**

$$\forall t: \operatorname{Source}\left(\right), (\forall u: \operatorname{Source}\left(\right), (\forall labels: \operatorname{RawMap}\left(\right), (\forall result: \operatorname{RawMap}\left(\right), (\forall next: \mathbb{Z}, (\forall after: \mathbb{Z}, (\forall x: \operatorname{Value}\left(\right), (\forall y: \operatorname{Value}\left(\right), ((\operatorname{nativeRun}\left(t, labels, next, x, \operatorname{calls}\left(t\right)\right) = \operatorname{some}\left(\operatorname{tuple}\left(u, result, after, y\right)\right)) \Rightarrow ((after = (next) + (\operatorname{length}\left(\operatorname{fresh}\left(t\right)\right))) \land ((\forall i: \mathbb{Z}, ((\operatorname{lt}\left(i, next\right)) \Rightarrow ((\operatorname{apply}\left(labels, i\right) \in \operatorname{terminals}\left(t\right)) \Rightarrow (\operatorname{apply}\left(result, i\right) = \operatorname{inherited}\left(t, \operatorname{apply}\left(labels, i\right)\right))))) \land (\forall j: \mathbb{N}, ((\operatorname{lt}\left(j, \operatorname{length}\left(\operatorname{fresh}\left(t\right)\right)\right)) \Rightarrow (\operatorname{apply}\left(result, (next) + (j)\right) = \operatorname{get}\left(\operatorname{fresh}\left(t\right), j\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorBindings.raw_bindings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RawMap is the actual integer-to-terminal address table used by nativeRun. The integer next is the next fresh identifier, above every authentic original identifier. Inherited follows alpha to LL and beta to LLL, with original branch prefixes unchanged. Fresh lists alpha R and beta R then LR, in allocation order under the fixed left-to-right original-leaf traversal. The theorem proves every old binding below next and every newly allocated integer destination, and the final next integer. At beta, R and LR are distinct addresses and receive different successive integers. No numerical call or pre-growth Tick occurs. Authentic original completeness, genuine grants, framing and physical conformance remain installation premises.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorBindings.raw_bindings`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth](NativeFreshSensorGrowth.md)
