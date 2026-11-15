# Increasing scans of the entire free region

## Abstract

Right-scan Hamming estimate and common-false reset criterion.

Write W(n) for Fin n to Bool, C(k,n,F,x) for completions, and P(s,F,x,y,h,g) for the original prefixCoupling. The histories are arbitrary; h and g witness nonempty full legal completion fibers. The reset test and independent fallback branches are those of the original law.

**Theorem 1.1 (A common-false head prepares the reset test).**

$$(\forall (n:\mathbb{N}), ((\forall (i:\operatorname{Fin}\left(n\right)), ((\forall (t:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((((\forall (j:\operatorname{Fin}\left(n\right)), (((j \in t) \implies (i < j))))) \implies ((((\forall (j:\operatorname{Fin}\left(n\right)), (((\neg (j \in \operatorname{insert}\left(i, F\right))) \implies (j \in t))))) \implies ((((\forall (j:\operatorname{Fin}\left(n\right)), (((j \in F) \implies (((i < j) \implies (\operatorname{eval}\left(x, j\right) = \operatorname{eval}\left(y, j\right)))))))) \implies (\operatorname{resetReady}\left(\operatorname{insert}\left(i, F\right), \operatorname{update}\left(x, i, \operatorname{false}\right), \operatorname{update}\left(y, i, \operatorname{false}\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming.reset_ready_after_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let i be the head and t the remaining scan. Every site in t is strictly greater than i, and every coordinate outside insert(i,F) belongs to t. Thus all coordinates through i belong to insert(i,F). If the original histories agree at fixed coordinates beyond i, updating both head bits to false satisfies resetReady. This fact also gives the zero remaining-cost branch of right_scan_hamming.

**Theorem 1.2 (Expected internal Hamming cost for an increasing scan).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (s:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), (((((\operatorname{Nodup}\left(s\right)) \land ((\forall (i:\operatorname{Fin}\left(n\right)), ((\forall (j:\operatorname{Fin}\left(n\right)), (((\operatorname{Before}\left(s, i, j\right)) \implies (\operatorname{val}\left(i\right) < \operatorname{val}\left(j\right)))))))))) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((((((\forall (i:\operatorname{Fin}\left(n\right)), (((i \in s) \implies (\neg (i \in F)))))) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((\neg (i \in F)) \implies (i \in s))))))) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), ((((\forall (i:\operatorname{Fin}\left(n\right)), ((\forall (j:\operatorname{Fin}\left(n\right)), (((((i \in s) \land (j \in F) \land (\operatorname{val}\left(i\right) < \operatorname{val}\left(j\right)))) \implies (\operatorname{at}\left(x, j\right) = \operatorname{at}\left(y, j\right)))))))) \implies (\operatorname{ExpectedHamming}\left(\operatorname{P}\left(s, F, x, y, h, g\right), s\right) \leq 1))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming.right_scan_hamming` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ExpectedHamming(J,s) is the sum over full-word pairs w of J(w)H(s,w). Before(s,i,j) means that i occurs strictly before j in the list s. H(s,w) denotes scanHamming: the sum of the zero-one disagreement indicators at the listed sites. The list is strictly increasing and lists the entire complement of F without repetitions. The fixed histories agree at every fixed site farther right than any scanned site. A supported common-zero branch has zero remaining cost, by screening and the reset law. In every other branch the current indicator is at most one, and the recursive expected remaining cost is at most one. Those branches have total mass at most one half, derived from conditional_step_coupling. Their weighted cost is therefore at most one. This estimate uses the same full-word joint law as the marginal theorem. The theorem covers short words and arbitrary nonempty completion fibers; it does not assert reflection, the geometric survival tail, or the final two-orientation contiguous-block assembly.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming.reset_ready_after_false`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming.right_scan_hamming`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling](KBonacciConditionalBlockCoupling.md)
