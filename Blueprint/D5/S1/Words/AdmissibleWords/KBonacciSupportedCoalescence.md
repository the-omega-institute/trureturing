# Complete outputs of the stopped recursion

## Abstract

Supported common-false coalescence of the native conditional prefix coupling.

Write W(n) for Fin n to Bool, C(k,n,F,x) for completions, and P(s,F,x,y,h,g) for the original prefixCoupling. The histories x and y are arbitrary; h and g assert that their full legal completion fibers are nonempty. The law tests resetReady before scanning, chooses an actual completion representative for reset transport, and retains both independent fallback branches for impossible child fibers.

**Theorem 1.1 (An emitted common false forces equality at all later scanned positions).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (s:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), (((\operatorname{Nodup}\left(s\right)) \implies (((\operatorname{StrictlyIncreasing}\left(s\right)) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((((\forall (i:\operatorname{Fin}\left(n\right)), (((i \in s) \implies (\neg (i \in F)))))) \implies ((((\forall (i:\operatorname{Fin}\left(n\right)), (((\neg (i \in F)) \implies (i \in s))))) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), (((\operatorname{FarSame}\left(s, F, x, y\right)) \implies ((\forall (w:\operatorname{Pair}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Bool}), (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})\right)), (((\operatorname{P}\left(s, F, x, y, h, g, w\right) \neq 0) \implies ((\forall (r,q:\operatorname{Fin}\left(\operatorname{length}\left(s\right)\right)), (((r \leq q) \implies (((\operatorname{fst}\left(w, \operatorname{get}\left(s, r\right)\right) = \operatorname{false}) \implies (((\operatorname{snd}\left(w, \operatorname{get}\left(s, r\right)\right) = \operatorname{false}) \implies (\operatorname{fst}\left(w, \operatorname{get}\left(s, q\right)\right) = \operatorname{snd}\left(w, \operatorname{get}\left(s, q\right)\right)))))))))))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The list s is duplicate-free, strictly increasing in coordinate value, and enumerates exactly the complement of F. FarSame(s,F,x,y) means that x(t)=y(t) whenever i is in s, t is in F and i<t. For any supported complete pair w, a common false at position r implies equality at every position q at or after r. This includes r=q, initially ready resets, equal histories, empty scans, n=0 and empty fixed sets.

In a reset branch, map support expresses the complete pair as (u,resetMap(z,y,u)) for the actual chosen reset coordinate z. Every free site lies strictly after z and is therefore equal on both sides. In a recursive branch, bind support retains the same complete output in a supported child. Both refined fibers are then nonempty. Exact native marginals and coupled_fixed recover the sampled head bits. If r is the head, these bits are both false, so the refined histories pass resetReady; its chosen coordinate need not be the head. If r is later, induction applies to the child, including a child already reset. Strict order, complement cover and farther fixed agreement descend with the refined histories.

Application to the same native joint law. Retain every hypothesis of `D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence` and apply the event estimate from `D5/S1/Words/AdmissibleWords/KBonacciEmittedTail.prefix_coupling_emitted_tail` to exactly the same P. Neither supplier declaration individually states the combined inequalities below.

Thus k>0 and n is natural; s is duplicate-free, strictly increasing in coordinate value, and enumerates exactly the complement of F. The arbitrary histories x and y have nonempty original completion fibers, and x(t)=y(t) whenever i is in s, t is in F, and i<t. No legality assumption is imposed on the histories themselves. Put m=length(s) and a=1/2 in ENNReal. Keep P=P(s,F,x,y,h,g), including its initial resetReady test, actual completion choices and both independent fallback branches.

For q in Fin(m), use the zero-based index q to define D(q,w) as the ENNReal indicator of disagreement between w.1(s[q]) and w.2(s[q]). Let H(s,w) be the sum of these indicators, namely scanHamming(s,w). Each free site is counted exactly once. This index corresponds to position q+1 in a one-based block scan; the index correspondence alone does not identify the native law with a paper construction.

$$
\begin{aligned}\operatorname{D}\left(q, w\right) = \operatorname{indicator}\left(\operatorname{fst}\left(w, \operatorname{get}\left(s, q\right)\right) \neq \operatorname{snd}\left(w, \operatorname{get}\left(s, q\right)\right)\right)\\\operatorname{H}\left(s, w\right) = \sum_{q \in \operatorname{Fin}\left(m\right)} \operatorname{D}\left(q, w\right) = \operatorname{scanHamming}\left(s, w\right)\end{aligned}
$$

Define A(j,w) to mean that no coordinate in s.take(j) has both emitted bits false. It permits (true,true), so it is not an event of disagreement at every position. For a supported complete output w and any r at or before q, a common false at r forces agreement at q by supported coalescence. Consequently disagreement at q excludes every common false among the first q+1 outputs. Outside support P(w)=0; the weighted inequality therefore holds for every complete pair, even if event inclusion fails off support.

$$
(\forall (q:\operatorname{Fin}\left(m\right)), ((\forall (w:\operatorname{Pair}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Bool}), (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})\right)), (\operatorname{P}\left(w\right) \operatorname{D}\left(q, w\right) \leq \operatorname{P}\left(w\right) \operatorname{indicator}\left(\operatorname{A}\left(q+1, w\right)\right)))))
$$

Here indicator(A(j)) denotes the ENNReal-valued function of w. Sum the weighted inequality over complete pairs and apply the emitted-tail estimate at j=q+1, which is at most m because q belongs to Fin(m). This gives both the probability of disagreement at q and its mean bound under the unchanged native P.

$$
(\forall (q:\operatorname{Fin}\left(m\right)), (\operatorname{mean}\left(P, \operatorname{D}\left(q\right)\right) \leq \operatorname{mean}\left(P, \operatorname{indicator}\left(\operatorname{A}\left(q+1\right)\right)\right) \leq a^{q+1}))
$$

Both W(n) times W(n) and Fin(m) are finite. Expanding mean as its nonnegative sum, using tsum_fintype, distributing multiplication across the finite scan sum, and commuting the two finite sums yields the mean of H as the sum of the means of D. Apply the pointwise bounds term by term under this one P. No independence between disagreement events is assumed.

$$
\begin{aligned}\operatorname{mean}\left(P, \operatorname{H}\left(s\right)\right) = \sum_{q \in \operatorname{Fin}\left(m\right)} \operatorname{mean}\left(P, \operatorname{D}\left(q\right)\right)\\\operatorname{mean}\left(P, \operatorname{H}\left(s\right)\right) \leq \sum_{q \in \operatorname{Fin}\left(m\right)} a^{q+1} = 1-a^{m}\end{aligned}
$$

For the geometric identity first work in NNReal with b=1/2. The finite geometric-sum identity says that the sum of b^q for 0<=q<m, multiplied by 1-b, equals 1-b^m. Since 1-b=b, this is the sum of b^(q+1). Coercion from NNReal to ENNReal preserves the finite sum and powers, and ENNReal.coe_sub preserves the truncated subtraction. Thus the sum of a^(q+1) is 1-a^m in ENNReal as used above. Since b^m<=1 and all quantities are finite, no cancellation involving infinity is needed.

For m=0 the pointwise assertion is vacuous, the Hamming sum is zero and 1-a^0=0; n=0 is included. If m>0, the last index q=m-1 uses precisely A(m), retaining the full-scan endpoint and exponent m. Empty F, equal histories, initial resets and k=1 remain within the stated hypotheses. These applications neither exclude degenerate inputs nor replace the coupling.

The original native completion-law marginals are already established. What remains for the book application is the exact identification of the relevant completion fibers, restricted laws and exterior-restored laws with its intended block refresh distributions. Simultaneous Fin.rev transport of both outputs, support and events is still required for a reflected left block. Equality in law with the paper shared-threshold coupling is not asserted and does not follow from these inequalities. The complete paper P2E application and any physical Hamiltonian identification retain their separate boundaries. This narrative is an application of existing results, with no additional Lean declaration or theorem attribution.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciEmittedTail.prefix_coupling_emitted_tail`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming](KBonacciRightScanHamming.md)
