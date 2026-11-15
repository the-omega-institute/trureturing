# The full-output no-common-false event

## Abstract

Geometric emitted-event tail for the original conditional zero-reset coupling.

Write W(n) for Fin n to Bool. C(k,n,F,x) is completions: all original DBonacciAdmissible full words agreeing with x at every site in F. L(F,x,h) is completionLaw on this nonempty fiber, and P(s,F,x,y,h,g) is the original prefixCoupling defined in KBonacciConditionalBlockCoupling. It tests resetReady before scanning and uses recursive refinement with an independent fallback. The finite set F may include the full exterior and sampled prefix.

**Theorem 1.1 (Geometric tail of the original emitted no-common-false event).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (s:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), (((\operatorname{Nodup}\left(s\right)) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((((\forall (i:\operatorname{Fin}\left(n\right)), (((i \in s) \implies (\neg (i \in F)))))) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), ((\forall (j:\mathbb{N}), (((j \leq \operatorname{length}\left(s\right)) \implies (\operatorname{MassEvent}\left(\operatorname{P}\left(s, F, x, y, h, g\right), s, j\right) \leq (1/2)^{j}))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciEmittedTail.prefix_coupling_emitted_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a full-word pair w, E(s,j,w) means that for every site i in s.take(j), the two emitted bits are not both false. The notation MassEvent(P,s,j) is mean P (fun w => if E(s,j,w) then 1 else 0). This includes (true,true), j=0 and the entire scan. No increasing-order or complement-cover assumption is needed for this event estimate. A counting induction in the original completion fibers bounds the all-true event by 2^(-j). This handles the original reset branch, whose two outputs agree at every free site. In a supported recursive child, the emitted head is the sampled bit pair. The common-false child contributes zero; the other children carry the residual event bound and have total mass at most one half. Impossible refinements have zero joint mass. The resulting induction uses the original prefixCoupling without modifying its fallback or initial-reset tests. Supported coalescence after an emitted common false is a separate assertion and is not proved here.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciEmittedTail.prefix_coupling_emitted_tail`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling](KBonacciConditionalBlockCoupling.md)
