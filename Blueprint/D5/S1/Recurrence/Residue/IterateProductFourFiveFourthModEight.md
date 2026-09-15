# The Fourth Compositional Iterate Modulo Eight

## Abstract

Every coefficient above degree two in the fourth compositional iterate of A396798 is divisible by eight.

Let A denote `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`, the unique integer ordinary formal power series with zero constant coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and I(k+1)(F)=Ik(F) composed with F. The product is ordinary series multiplication, and the coefficients have no factorial scaling.

**Theorem 1.1 (Hanna's fourth conjecture).**

$$\forall n:\mathbb{N}, 2<n\implies 8 \mid \operatorname{coeff}\left(n, \operatorname{iterate}\left(A, 4\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396798-fourth-iterate-mod-eight` (proved) by `D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396798-fourth-iterate-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396798: compositional iterates modulo eight*. URL: <https://oeis.org/A396798>.

*Commentary.*

Modulo four, source uniqueness identifies A with X/(1-X), so its second iterate equals X+2X^2. An exact integer quotient gives G=X+2X^2+4B for the second iterate modulo eight. Its zero constant coefficient makes substitution legitimate. The relations 4(G-X)=0 and 4((B composed with G)-B)=0, together with 2G^2=2X^2, yield G composed with G=X+4X^2. Thus every coefficient of the fourth iterate above degree two vanishes modulo eight.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight](IterateProductFourFiveEighthModEight.md)
