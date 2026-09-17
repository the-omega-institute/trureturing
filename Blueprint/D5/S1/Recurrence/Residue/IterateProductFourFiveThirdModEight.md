# The Third Compositional Iterate Modulo Eight

## Abstract

The third compositional iterate of A396798 has coefficient period 3,1,7,5 modulo eight from degree two.

Let A denote `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`, the unique integer ordinary formal power series with zero constant coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and I(k+1)(F)=Ik(F) composed with F. The product is ordinary series multiplication, with no factorial scaling.

**Theorem 1.1 (Hanna's third conjecture).**

$$\forall n:\mathbb{N}, 1<n\implies 8 \mid (\operatorname{coeff}\left(n, \operatorname{iterate}\left(A, 3\right)\right) - (\operatorname{if} \operatorname{mod}\left((n - 2), 4\right) = 0 \operatorname{then} 3 \operatorname{else} \operatorname{if} \operatorname{mod}\left((n - 2), 4\right) = 1 \operatorname{then} 1 \operatorname{else} \operatorname{if} \operatorname{mod}\left((n - 2), 4\right) = 2 \operatorname{then} 7 \operatorname{else} 5))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396798-third-iterate-mod-eight` (proved) by `D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396798-third-iterate-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396798: compositional iterates modulo eight*. URL: <https://oeis.org/A396798>.

*Commentary.*

Reduce A modulo eight to F, and let J=I5(F). The fifth coefficient identity gives the rational form of J. Clearing unit denominators identifies its compositional inverse K=X+X^2*(3+X+7*X^2+5*X^3)/(1-X^4). The eighth identity I8(F)=X identifies I3(F) with K. The geometric inverse of 1-X^4 then gives the period 3,1,7,5 from degree two.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight](IterateProductFourFiveEighthModEight.md)
- Dependency: [D5/S1/Recurrence/Residue/IterateProductFourFiveFifthModEight](IterateProductFourFiveFifthModEight.md)
