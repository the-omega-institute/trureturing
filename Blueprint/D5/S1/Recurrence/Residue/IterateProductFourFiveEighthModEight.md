# The Eighth Compositional Iterate Modulo Eight

## Abstract

Every coefficient above degree one in the eighth compositional iterate of A396798 is divisible by eight.

Write I0(F)=X and I(k+1)(F)=Ik(F) composed with F. The source is an ordinary integer formal series satisfying A=X+I4(A)*I5(A), with zero constant coefficient. The product is ordinary series multiplication, and no factorial scaling is used. Let H(F)=X+I4(F)*I5(F). In the definition below, iterateFunction(H,k,0) means H applied k times to zero, and mk assembles a series from its coefficient function.

**Definition 1.1 (The source series).**

$$A=\operatorname{mk}\left(n\mapsto\operatorname{coeff}\left(n, \operatorname{iterateFunction}\left(H, n+1, 0\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396798: the fourth and eighth compositional iterates modulo eight*. URL: <https://oeis.org/A396798>.

*Commentary.*

The n-th coefficient is taken from H iterated n+1 times at the zero series. The result's proof establishes coefficient stabilization, the source equation and uniqueness among zero-constant fixed points.

**Theorem 1.2 (Hanna's eighth conjecture).**

$$\forall n:\mathbb{N}, 1<n\implies 8 \mid \operatorname{coeff}\left(n, \operatorname{iterate}\left(A, 8\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396798-eighth-iterate-mod-eight` (proved) by `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396798-eighth-iterate-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396798: the fourth and eighth compositional iterates modulo eight*. URL: <https://oeis.org/A396798>.

*Commentary.*

For every natural index n>1, the coefficient of the eighth compositional iterate is divisible by eight. Source uniqueness identifies A modulo four with X/(1-X). An exact integer quotient and square-zero iteration then yield the eighth iterate equal to X modulo eight. This resolves only the eighth comment of OEIS revision 12; the other comments retain their separate scopes and evidence.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.result`
- Dependency: [D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix](../Invariants/ThreeFourIterateProductModSix.md)
- Dependency: [D5/S1/Recurrence/Parity/DiagonalIterateEven](../Parity/DiagonalIterateEven.md)
- Dependency: [D5/S1/Recurrence/Residue/IterateProductTwentyFiveModFive](IterateProductTwentyFiveModFive.md)
