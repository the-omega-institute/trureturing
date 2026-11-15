# Complete outputs of the stopped recursion

## Abstract

Supported common-false coalescence of the native conditional prefix coupling.

Write W(n) for Fin n to Bool, C(k,n,F,x) for completions, and P(s,F,x,y,h,g) for the original prefixCoupling. The histories x and y are arbitrary; h and g assert that their full legal completion fibers are nonempty. The law tests resetReady before scanning, chooses an actual completion representative for reset transport, and retains both independent fallback branches for impossible child fibers.

**Theorem 1.1 (A common-false head prepares the reset test).**

$$(\forall (n:\mathbb{N}), ((\forall (i:\operatorname{Fin}\left(n\right)), ((\forall (t:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((((\forall (j:\operatorname{Fin}\left(n\right)), (((j \in t) \implies (i < j))))) \implies ((((\forall (j:\operatorname{Fin}\left(n\right)), (((\neg (j \in \operatorname{insert}\left(i, F\right))) \implies (j \in t))))) \implies ((((\forall (j:\operatorname{Fin}\left(n\right)), (((j \in F) \implies (((i < j) \implies (\operatorname{eval}\left(x, j\right) = \operatorname{eval}\left(y, j\right)))))))) \implies (\operatorname{resetReady}\left(\operatorname{insert}\left(i, F\right), \operatorname{update}\left(x, i, \operatorname{false}\right), \operatorname{update}\left(y, i, \operatorname{false}\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_ready_after_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let i be the head and t the remaining scan. Every site in t is strictly greater than i, and every coordinate outside insert(i,F) belongs to t. Thus all coordinates through i belong to insert(i,F). If the original histories agree at fixed coordinates beyond i, updating both head bits to false satisfies resetReady. This fact also gives the zero remaining-cost branch of right_scan_hamming.

**Theorem 1.2 (An emitted common false forces equality at all later scanned positions).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (s:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), (((\operatorname{Nodup}\left(s\right)) \implies (((\operatorname{StrictlyIncreasing}\left(s\right)) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((((\forall (i:\operatorname{Fin}\left(n\right)), (((i \in s) \implies (\neg (i \in F)))))) \implies ((((\forall (i:\operatorname{Fin}\left(n\right)), (((\neg (i \in F)) \implies (i \in s))))) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), (((\operatorname{FarSame}\left(s, F, x, y\right)) \implies ((\forall (w:\operatorname{Pair}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Bool}), (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})\right)), (((\operatorname{P}\left(s, F, x, y, h, g, w\right) \neq 0) \implies ((\forall (r,q:\operatorname{Fin}\left(\operatorname{length}\left(s\right)\right)), (((r \leq q) \implies (((\operatorname{fst}\left(w, \operatorname{get}\left(s, r\right)\right) = \operatorname{false}) \implies (((\operatorname{snd}\left(w, \operatorname{get}\left(s, r\right)\right) = \operatorname{false}) \implies (\operatorname{fst}\left(w, \operatorname{get}\left(s, q\right)\right) = \operatorname{snd}\left(w, \operatorname{get}\left(s, q\right)\right)))))))))))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The list s is duplicate-free, strictly increasing in coordinate value, and enumerates exactly the complement of F. FarSame(s,F,x,y) means that x(t)=y(t) whenever i is in s, t is in F and i<t. For any supported complete pair w, a common false at position r implies equality at every position q at or after r. This includes r=q, initially ready resets, equal histories, empty scans, n=0 and empty fixed sets.

In a reset branch, map support expresses the complete pair as (u,resetMap(z,y,u)) for the actual chosen reset coordinate z. Every free site lies strictly after z and is therefore equal on both sides. In a recursive branch, bind support retains the same complete output in a supported child. Both refined fibers are then nonempty. Exact native marginals and coupled_fixed recover the sampled head bits. If r is the head, these bits are both false, so the refined histories pass resetReady; its chosen coordinate need not be the head. If r is later, induction applies to the child, including a child already reset. Strict order, complement cover and farther fixed agreement descend with the refined histories. This support implication combines with the separate native emitted-tail estimate at the book's scan interface. Simultaneous Fin.rev transport and the final pointwise and Hamming assembly require additional results.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_ready_after_false`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling](KBonacciConditionalBlockCoupling.md)
