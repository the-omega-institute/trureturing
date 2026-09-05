# Green Mass and Description-Cost Separation

## Abstract

Green mass and description cost vary independently on one binary table carrier.

**Theorem 1.1 (Equal Green mass permits distinct description costs).**

$$\begin{gathered}\forall c: \mathbb{N}, M: \operatorname{BinaryDescriptionMachine}\left(c\right),\\{}\forall S: \operatorname{Finset}\left(\mathbb{N}\right), t: \mathbb{N} \to \operatorname{Fin}\left(2\right),\\{}\mu:=\operatorname{stringMeasure}\left(\operatorname{Fin}\left(2\right)\right),\\{}(\forall J: \operatorname{Type}, [\operatorname{Countable}(J)],\\{}\forall systems: J \to \operatorname{NamingSystem}\left(\mathbb{N} \to \operatorname{Fin}\left(2\right)\right),\\{}\mu(\operatorname{greenClass}\left(S, t\right)) = \operatorname{inv}\left(\operatorname{card}\left(\operatorname{Fin}\left(2\right)\right)\right)^{\operatorname{card}\left(S\right)} \land \\{}0 < \mu(\operatorname{greenClass}\left(S, t\right)) \land \\{}\operatorname{Countable}\left(\operatorname{iUnion}\left((j: J \mapsto \operatorname{named}\left(\operatorname{systems}\left(j\right)\right))\right)\right) \land \\{}\mu(\operatorname{iUnion}\left((j: J \mapsto \operatorname{named}\left(\operatorname{systems}\left(j\right)\right))\right)) = 0 \land \\{}\mu(\operatorname{iUnion}\left((j: J \mapsto \operatorname{named}\left(\operatorname{systems}\left(j\right)\right))\right)^{c}) = 1 \land \\{}\forall j: J, Q: \mathbb{N}, \mu(\left\{\exists a: \operatorname{Name}\left(\operatorname{systems}\left(j\right)\right), a \in \operatorname{layer}\left(\operatorname{systems}\left(j\right), Q\right) \land \operatorname{assignment}\left(\operatorname{systems}\left(j\right), a\right) = \operatorname{some}\left(x\right) \mid x \in \mathbb{N} \to \operatorname{Fin}\left(2\right)\right\}^{c}) = 1) \land \\{}(\forall l: \mathbb{N}, \mu(\operatorname{greenClass}\left(\operatorname{range}\left(l\right), (k: \mathbb{N} \mapsto 0)\right)) = \operatorname{pow}\left(\operatorname{inv}\left(\operatorname{card}\left(\operatorname{Fin}\left(2\right)\right)\right), l\right) \land \\{}\operatorname{descriptionComplexity}\left(\operatorname{objects}\left(M, l\right), \operatorname{zero}\left(\operatorname{Fin}\left(l\right) \to \operatorname{Fin}\left(2\right)\right)\right) \leq 2 \times \operatorname{natLog}\left(2, l + 1\right) + c) \land \\{}(\forall l: \mathbb{N}, 2 \times \operatorname{natLog}\left(2, l + 1\right) + c < l \implies \\{}\exists r: \operatorname{Fin}\left(l\right) \to \operatorname{Fin}\left(2\right), u: \mathbb{N} \to \operatorname{Fin}\left(2\right),\\{}(\forall i: \operatorname{Fin}\left(l\right), \operatorname{u}\left(i\right) = \operatorname{r}\left(i\right)) \land \\{}\operatorname{descriptionComplexity}\left(\operatorname{objects}\left(M, l\right), \operatorname{zero}\left(\operatorname{Fin}\left(l\right) \to \operatorname{Fin}\left(2\right)\right)\right) < \operatorname{descriptionComplexity}\left(\operatorname{objects}\left(M, l\right), r\right) \land \\{}\mu(\operatorname{greenClass}\left(\operatorname{range}\left(l\right), u\right)) = \operatorname{pow}\left(\operatorname{inv}\left(\operatorname{card}\left(\operatorname{Fin}\left(2\right)\right)\right), l\right) \land \\{}\mu(\operatorname{greenClass}\left(\operatorname{range}\left(l\right), (k: \mathbb{N} \mapsto 0)\right)) = \operatorname{pow}\left(\operatorname{inv}\left(\operatorname{card}\left(\operatorname{Fin}\left(2\right)\right)\right), l\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/GreenMassDescriptionSeparation.green_mass_naming_conservation_and_description_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a binary description machine with compiler overhead c. On the same binary sequence carrier, a finite support and target retain the exact Green-class mass while every countable naming family and every finite height layer leave a full-measure anonymous complement.

At every length l, the all-zero table has Green mass exactly 2^(-l) and description complexity at most 2 log_2(l+1)+c. Thus arbitrarily deep finite certificates can remain succinctly described while their residual mass follows the independent budget exponent.

Whenever the logarithmic zero-code bound is below l, an incompressible mask has strictly greater description complexity. Extending that mask to a binary sequence gives a Green class with exactly the same mass as the zero table at the same support budget.

The proof directly applies the frozen conservation and incompressible-XOR owners. The new conclusion couples their public outputs on one carrier; it neither replaces the Green class nor assumes the desired separation.

## References

- Truth anchor: `D5/S0/Naming/Conservation/GreenMassDescriptionSeparation.green_mass_naming_conservation_and_description_separation`
- Dependency: [D5/S0/Computability/DescriptionComplexity/XorTransformationTightness](../../Computability/DescriptionComplexity/XorTransformationTightness.md)
- Dependency: [D5/S0/Naming/Conservation/GreenClassNamingConservation](GreenClassNamingConservation.md)
