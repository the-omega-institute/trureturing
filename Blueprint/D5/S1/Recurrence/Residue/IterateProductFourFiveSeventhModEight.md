# The Seventh Compositional Iterate Modulo Eight

## Abstract

The seventh compositional iterate of A396798 has coefficient period 7,1,3,5 modulo eight from degree two.

Let A denote `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`, the unique integer ordinary formal power series with zero constant coefficient satisfying A=X+I4(A)*I5(A). Write I0(F)=X and I(k+1)(F)=Ik(F) composed with F. The product is ordinary series multiplication, with no factorial scaling.

**Theorem 1.1 (Hanna's seventh conjecture).**

$$\forall n:\mathbb{N}, 1<n\implies 8 \mid (\operatorname{coeff}\left(n, \operatorname{iterate}\left(A, 7\right)\right) - (\operatorname{if} \operatorname{mod}\left((n - 2), 4\right) = 0 \operatorname{then} 7 \operatorname{else} \operatorname{if} \operatorname{mod}\left((n - 2), 4\right) = 1 \operatorname{then} 1 \operatorname{else} \operatorname{if} \operatorname{mod}\left((n - 2), 4\right) = 2 \operatorname{then} 3 \operatorname{else} 5))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396798-seventh-iterate-mod-eight` (proved) by `D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396798-seventh-iterate-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396798: compositional iterates modulo eight*. URL: <https://oeis.org/A396798>.

*Commentary.*

Reduce A modulo eight to F, and set U=I3(F). The source definition gives coeff0(F)=0 and coeff1(F)=1. The existing iterate_top theorem, comparing F with X at degree two, gives coeff2(Ij(F))=j*coeff2(F). The public third result at n=2 gives 3*coeff2(F)=3; since 3*3=1 modulo eight, coeff2(F)=1. These low coefficients and the public fourth tail give I4(F)=X+4X^2. Iteration addition and substitution into U give I7(F)=U+4U^2. The zero constant and unit linear coefficients of U, together with the third period, give 4*coeff m(U)=4 for every m>0. The convolution endpoints vanish, and its n-1 positive-index pairs each contribute four, so 4*coeff n(U^2)=4*(n-1) for n>1. The four cases of (n-2)%4 give 7,1,3,5; compatibility of coefficient reduction with iteration transfers this identity to integer divisibility.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight](IterateProductFourFiveFourthModEight.md)
- Dependency: [D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight](IterateProductFourFiveThirdModEight.md)
