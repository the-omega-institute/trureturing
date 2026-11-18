# Absorb the original-range powers and logarithms

## Abstract

The actual weighted chart error and moment error are absorbed into A*p^epsilon in the original area range.

**Theorem 1.1 (The actual moment error permits exponents up to fifteen quarters).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates.range_error_absorption_of_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates.range_error_absorption_of_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha<=15/4, epsilon>0, C>=1 and K>0, the same actual chart and moment expression is at most D*A*p^epsilon whenever p>=2 and 0<=A<=C*p^alpha. The proof uses alpha<=4 and 4*alpha<=15, so A/p^4<=C and A^4/p^15<=C^4. The original theorem below consumes this stronger estimate at alpha=18/5. The analytic estimate alone does not supply any endpoint count, singular-factor cover or larger range for the original conjecture.

**Theorem 1.2 (One uniform final analytic estimate).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates.original_range_error_absorption`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates.original_range_error_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix epsilon>0, C>=1 and K>0. There exists D>0, chosen before all real p>=2 and areas 0<=A<=C*p^(18/5), such that with L=1+log(2p)/log(2), the sum K*p^(epsilon/2)*[A*(1+L)+A^2/p^4]+sqrt(K*p^(epsilon/2)*A^6*L/p^15) is at most D*A*p^epsilon. The statement includes A=0, uses no counting estimate as a hypothesis, and needs no primality.

Set T=p^(epsilon/2) and B=2+1/[(epsilon/2)*log(2)]. The real logarithm inequality log(p)<=p^(epsilon/2)/(epsilon/2) proves L<=B*T, while T>=1 and T^2=p^epsilon. The original area cap and exponent comparisons 18/5<=4 and 72/5<=15 give A/p^4<=C and A^4/p^15<=C^4. The first term is at most K*(1+B+C)*A*T^2. Taking E=1+K*B*C^4 gives E^2>=K*B*C^4, so the radicand is at most (E*A*T)^2 and its square root is at most E*A*T^2. One may therefore take D=K*(1+B+C)+E. All logarithmic and power bounds are proved internally.

This is the analytic absorption of the actual chart estimates. Their original-variable, lattice, word and reconstruction hypotheses must still be supplied by their own theorems, and the bounded small-p tuple count remains separate. The full original conjecture and official acceptance are not asserted by this module.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates.original_range_error_absorption`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates.range_error_absorption_of_exponent`
