# Double Extensional Quotient Universality

## Abstract

The two-sided extensional quotient is uniquely equivalent to every extensional factorization.

**Theorem 1.1 (The double extensional quotient is universally minimal).**

$$\begin{gathered}\forall X, P, Lambda, XPrime, PPrime: Type,\\{}e: X \to P \to Lambda, a: X \to XPrime, b: P \to PPrime, ePrime: XPrime \to PPrime \to Lambda,\\{}\operatorname{Surjective}(a), \operatorname{Surjective}(b),\\{}\forall x: X, p: P, e(x)(p) = ePrime(a(x))(b(p)),\\{}\forall x: XPrime, y: XPrime, (\forall p: PPrime, ePrime(x)(p) = ePrime(y)(p)) \Rightarrow x = y,\\{}\forall p: PPrime, q: PPrime, (\forall z: XPrime, ePrime(z)(p) = ePrime(z)(q)) \Rightarrow p = q \Rightarrow\\{}\exists! E: \operatorname{Prod}(\operatorname{Equiv}(\operatorname{quotient}(\operatorname{ker}(\operatorname{stateBehavior}(e))), XPrime), \operatorname{Equiv}(\operatorname{quotient}(\operatorname{ker}(\operatorname{protocolBehavior}(e))), PPrime)),\\{}\forall x: X, \operatorname{fst}(E)(\operatorname{quotientClass}(\operatorname{ker}(\operatorname{stateBehavior}(e)), x)) = a(x) \land \forall p: P, \operatorname{snd}(E)(\operatorname{quotientClass}(\operatorname{ker}(\operatorname{protocolBehavior}(e)), p)) = b(p) \land \forall x: X, p: P, e(x)(p) = ePrime(\operatorname{fst}(E)(\operatorname{quotientClass}(\operatorname{ker}(\operatorname{stateBehavior}(e)), x)))(\operatorname{snd}(E)(\operatorname{quotientClass}(\operatorname{ker}(\operatorname{protocolBehavior}(e)), p))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source evaluation supplies a behavior row for every state and a behavior column for every protocol. The two canonical quotient carriers are the equality kernels of those rows and columns.

A pair of surjections to extensional target carriers, together with the commuting evaluation square, induces a unique equivalence from each canonical quotient. The displayed equations expose the canonical maps and their action on every source state and protocol.

No exact dual quotient theorem was found in D5 or pinned Mathlib. The proof uses quotient lifting, representative induction, and Equiv.ofBijective directly on the source evaluation primitives.

## References

- Truth anchor: `D5/S3/Observer/Completion/DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality`
