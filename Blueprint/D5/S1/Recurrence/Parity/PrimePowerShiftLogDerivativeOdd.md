# All Terms of OEIS A393867 Are Odd

## Abstract

Every coefficient of the logarithmic derivative defining OEIS A393867 is odd.

Let F be the integer series generatingSeries from PrimePowerShiftLogDerivative. Its constant coefficient is one, and coeff(n,F^prime(n)) = prime(n) coeff(n-1,F^prime(n)) for n >= 1. The nth term a393867(n) is coeff(n-1,F'/F). The cast in the first formula is reduction of an integer to ZMod 2; Odd in the second formula is integer oddness. The results use this original series and its one-based sequence indexing.

**Theorem 1.1 (Paired Coefficients Modulo Two).**

$$\forall m: \mathbb{N}, \operatorname{cast}\left(\operatorname{coeff}\left(2 \cdot m, F\right)\right) = \operatorname{cast}\left(\operatorname{coeff}\left(2 \cdot m + 1, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.generating_coeff_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A393867, logarithmic derivative of A393866 (g.f. with [x^n] A^prime(n) = prime(n) [x^(n-1)] A^prime(n))*. URL: <https://oeis.org/A393867>.

*Commentary.*

Over ZMod 2 put D(B)=(1+X)B'-B. For an odd prime p, the power rule gives D(F^p)=D(F)F^(p-1). Every odd coefficient of D(B) vanishes identically. At even degree k>0, the source equation at n=k+1 gives coeff(k,D(F^p))=0. Strong induction removes the lower coefficients of D(F); the constant coefficient of F^(p-1) is one, so the kth coefficient of D(F) also vanishes. At k=0 the integral equation with p=2 first gives F_1=1. Extracting each even coefficient of D(F)=0 proves the displayed pair equality.

**Theorem 1.2 (The Oddness Conjecture).**

$$\forall n: \mathbb{N}, 1 \le n \implies \operatorname{Odd}\left(\operatorname{a393867}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.a393867_odd` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a393867-all-terms-odd` (proved) by `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.a393867_odd`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a393867-all-terms-odd","declaration_gid":"D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.a393867_odd","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A393867, logarithmic derivative of A393866 (g.f. with [x^n] A^prime(n) = prime(n) [x^(n-1)] A^prime(n))*. URL: <https://oeis.org/A393867>.

*Commentary.*

The paired coefficients give (1+X)F'=F after reduction modulo two. Multiplying by the mapped unit inverse of F gives (1+X)L=1, where L is the reduction of the original integer logarithmic derivative. Its constant coefficient is one, and consecutive coefficients are equal, so every coefficient is one in ZMod 2. The integer terms are therefore odd. This proves exactly the second A393867 comment, 'Conjecture: all terms are odd.'

## References

- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.a393867_odd`
- Truth anchor: `D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.generating_coeff_pair`
- Dependency: [D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative](PrimePowerShiftLogDerivative.md)
