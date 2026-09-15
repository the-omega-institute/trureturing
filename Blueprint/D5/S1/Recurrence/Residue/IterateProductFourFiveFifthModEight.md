# The Fifth Compositional Iterate Modulo Eight

## Abstract

The fifth compositional iterate of A396798 has coefficient period 5,1,1,5 modulo eight from degree two.

Let A denote `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`, the unique integer ordinary formal power series with zero constant coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and I(k+1)(F)=Ik(F) composed with F. The product is ordinary series multiplication, with no factorial scaling.

**Theorem 1.1 (Hanna's fifth conjecture).**

$$\forall n:\mathbb{N}, 1<n\implies 8 \mid (\operatorname{coeff}\left(n, \operatorname{iterate}\left(A, 5\right)\right) - (\operatorname{if} (\operatorname{mod}\left((n - 2), 4\right) = 0 \lor \operatorname{mod}\left((n - 2), 4\right) = 3) \operatorname{then} 5 \operatorname{else} 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396798-fifth-iterate-mod-eight` (proved) by `D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396798-fifth-iterate-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396798: compositional iterates modulo eight*. URL: <https://oeis.org/A396798>.

*Commentary.*

Reduce A modulo eight to F, and write P=I4(F) and J=I5(F). The fourth and eighth iterate identities give P=X+4X^2 and I8(F)=X. Substituting P into F=X+PJ gives J=P+XF. Elimination yields (J-X)(1-X^4)=5X^2+X^3+X^4+5X^5. The geometric inverse of 1-X^4 has coefficient one at multiples of four and zero elsewhere, so the stated period starts at degree two.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight](IterateProductFourFiveFourthModEight.md)
