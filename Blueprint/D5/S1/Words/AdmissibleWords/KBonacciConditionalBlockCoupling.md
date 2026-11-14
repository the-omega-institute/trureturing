# Full exterior and sampled prefix

## Abstract

Conditional next-bit couplings and zero screening for forbidden-run words.

Write W(n) for Fin n to Bool and A(k,n,w) for the original DBonacciAdmissible scanner. C(k,n,F,x) is the finite set of legal full words w satisfying w(i)=x(i) for every i in F. The fixed set F can contain the entire exterior of a contiguous block and any sampled prefix. Both ends remain fixed. L(F,x,h) is completionLaw, the uniform PMF on this fiber, where h states that the fiber is nonempty.

For PMFs p and q on Bool, J(p,q) denotes bitCoupling. Set a=p(false) and b=q(false). If a is at most b, its masses at (false,false), (false,true), (true,false), (true,true) are a, zero, b-a, one-b. Otherwise exchange the two coordinates of the same construction with a and b interchanged. This is the finite shared-threshold next-bit law.

**Theorem 1.1 (Exact conditional-bit marginals and a common zero).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), ((\forall (i:\operatorname{Fin}\left(n\right)), (((\neg (i \in F)) \implies (((\operatorname{mapFst}\left(\operatorname{J}\left(\operatorname{evalLaw}\left(F, x, h, i\right), \operatorname{evalLaw}\left(F, y, g, i\right)\right)\right) = \operatorname{evalLaw}\left(F, x, h, i\right)) \land (\operatorname{mapSnd}\left(\operatorname{J}\left(\operatorname{evalLaw}\left(F, x, h, i\right), \operatorname{evalLaw}\left(F, y, g, i\right)\right)\right) = \operatorname{evalLaw}\left(F, y, g, i\right)) \land (1/2 \leq \operatorname{mass}\left(\operatorname{J}\left(\operatorname{evalLaw}\left(F, x, h, i\right), \operatorname{evalLaw}\left(F, y, g, i\right)\right), \operatorname{false}, \operatorname{false}\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.conditional_step_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The laws p and q in the formula are the pushforwards of L(F,x,h) and L(F,y,g) by evaluation at i. Deleting the one at an unfixed coordinate gives an injection from one-completions into zero-completions while preserving all other bits. Thus each actual conditional zero mass is at least one half. The displayed joint law has exact marginals and common-zero mass equal to their minimum. No lower bound on word length relative to k is required.

**Theorem 1.2 (A common zero screens the earlier prefix).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (((((\operatorname{A}\left(k, n, x\right)) \land (\operatorname{A}\left(k, n, y\right)))) \implies ((\forall (z:\operatorname{Fin}\left(n\right)), (((((\operatorname{at}\left(x, z\right) = \operatorname{false}) \land (\operatorname{at}\left(y, z\right) = \operatorname{false}))) \implies ((\forall (t:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (\operatorname{A}\left(k, n, \operatorname{S}\left(x, z, t\right)\right) \iff \operatorname{A}\left(k, n, \operatorname{S}\left(y, z, t\right)\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.zero_screening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define S(x,z,t)(i) to be x(i) when i is at most z and t(i) otherwise. A forbidden window is either contained in the legal prefix, contained in the shared later assignment, or crosses z. The last possibility contains the specified zero. Hence replacing the legal prefix preserves the entire suffix-completion condition.

**Theorem 1.3 (Uniform suffix laws agree after reset).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (((((\operatorname{A}\left(k, n, x\right)) \land (\operatorname{A}\left(k, n, y\right)))) \implies ((\forall (z:\operatorname{Fin}\left(n\right)), (((((\operatorname{at}\left(x, z\right) = \operatorname{false}) \land (\operatorname{at}\left(y, z\right) = \operatorname{false}) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((\operatorname{val}\left(i\right) \leq \operatorname{val}\left(z\right)) \implies (i \in F))))) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((((i \in F) \land (\operatorname{val}\left(z\right) < \operatorname{val}\left(i\right)))) \implies (\operatorname{at}\left(x, i\right) = \operatorname{at}\left(y, i\right)))))))) \implies (((\operatorname{mapReset}\left(\operatorname{L}\left(F, x\right), y, z\right) = \operatorname{L}\left(F, y\right)) \land ((\forall (w:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (i:\operatorname{Fin}\left(n\right)), (((\operatorname{val}\left(z\right) < \operatorname{val}\left(i\right)) \implies (\operatorname{at}\left(\operatorname{S}\left(y, z, w\right), i\right) = \operatorname{at}\left(w, i\right)))))))) \land (((\operatorname{mapFst}\left(\operatorname{R}\left(F, x, y, z\right)\right) = \operatorname{L}\left(F, x\right)) \land (\operatorname{mapSnd}\left(\operatorname{R}\left(F, x, y, z\right)\right) = \operatorname{L}\left(F, y\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_law_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All coordinates through z are fixed. The two legal exterior words have a zero at z and agree at every fixed coordinate strictly after z. Prefix replacement S(y,z,w) is a bijection between their full completion fibers, with inverse S(x,z,w). It therefore transports the uniform conditional laws exactly. R(F,x,y,z) samples w from L(F,x) and returns the pair (w,S(y,z,w)); its two marginal pushforwards are exactly L(F,x) and L(F,y). Every coordinate strictly after z is preserved.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.conditional_step_coupling`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_law_transport`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.zero_screening`
- Dependency: [D5/S0/Tower/DBonacci/TerminalSampling](../../../S0/Tower/DBonacci/TerminalSampling.md)
- Dependency: [D5/S1/Words/ClosedRunStarts](../ClosedRunStarts.md)
