# Mod-Five Observer Diagonalization

## Abstract

The reflected Hurwitz sectors modulo five split into trivial and quadratic channels.

**Theorem 1.1 (Hadamard separation of the two reflected residue sectors).**

$$\forall s \in \mathbb{C},\; s \ne 1 \Rightarrow \left(5^{-s} \times (\left(H_{1}\right)\left(s\right) + \left(H_{2}\right)\left(s\right)) = (1 - 5^{-s}) \times \operatorname{riemannZeta}(s) \land \left(5^{-s} \times (\left(H_{1}\right)\left(s\right) - \left(H_{2}\right)\left(s\right)) = \operatorname{LFunction}(modFiveQuadraticCharacter, s) \land \left(\operatorname{vec2}((1 - 5^{-s}) \times \operatorname{riemannZeta}(s), \operatorname{LFunction}(modFiveQuadraticCharacter, s)) = 5^{-s} \times \operatorname{mulVec}(modFiveObserverHadamard, \operatorname{vec2}(\left(H_{1}\right)\left(s\right), \left(H_{2}\right)\left(s\right))) \land \left(5^{-s} \times (\left(H_{1}\right)\left(s\right) + \left(H_{2}\right)\left(s\right)) = \operatorname{LFunctionTrivChar}(5, s) \land \left(\operatorname{LFunctionTrivChar}(5, s) = (1 - 5^{-s}) \times \operatorname{riemannZeta}(s) \land \left(modFiveQuadraticCharacter\left(0\right) = 0 \land \left(modFiveQuadraticCharacter\left(1\right) = 1 \land \left(modFiveQuadraticCharacter\left(2\right) = -1 \land \left(modFiveQuadraticCharacter\left(3\right) = -1 \land modFiveQuadraticCharacter\left(4\right) = 1\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ModFiveObserverDiagonalization.mod_five_observer_diagonalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first channel is the sum of the Hurwitz zeta terms at residues one and four modulo five. The second channel uses residues two and three. Both are constructed with the canonical map from ZMod 5 to the unit additive circle.

The canonical quadratic character modulo five has values zero, one, minus one, minus one, and one. Consequently the sum and difference of the channels are the trivial and quadratic Dirichlet L-functions.

The unnormalized two-by-two Hadamard matrix packages the two scalar identities. The trivial-character clause records that restoring the deleted Euler factor at five gives the Riemann zeta channel.

The point s = 1 is excluded because the pointwise trivial-character Euler-factor identity is used away from its pole.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ModFiveObserverDiagonalization.mod_five_observer_diagonalization`
