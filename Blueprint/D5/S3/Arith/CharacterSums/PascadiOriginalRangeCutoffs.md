# Discharge the original-range numerical cutoffs

## Abstract

The original area cap supplies the numerical endpoint and bad-degree hypotheses uniformly at large p.

**Theorem 1.1 (The exact area exponent and an explicit uniform threshold).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalRangeCutoffs.original_range_numeric_cutoffs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalRangeCutoffs.original_range_numeric_cutoffs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real C>=1, nonnegative area A and real parameter p, assume A<=C*p^(18/5) and p>[2^20*(1+C)]^200. Then the choice M=32C supplies all four numerical conclusions: (32A/p^3)^5<=(32C)^5*p^3, A<p^4, (10368*3^9)^5*(32C)^35<p^4, and (24*(8*18)^4)^5*(32C)^40<p. The threshold depends only on the original cap constant C. Primality is not needed for these real inequalities.

Raise the original area bound to the fifth power. The real-power identity (p^(18/5))^5=p^18 gives A^5<=C^5*p^18 and hence the exact endpoint height cap after division by p^15. Write D=2^20*(1+C). The strict threshold yields C^5<p^2, so A^5<p^20 and A<p^4. Both fixed endpoint constants are bounded by D^10, while 32C<=D; their products with (32C)^35 and (32C)^40 are bounded by D^45 and D^50, respectively, and hence are less than p. This also implies the required p^4 separation.

This discharges numerical hypotheses of the actual long-chart bad-degree average in the original large-p range. It does not assume a height or counting bound. The bounded small-p range remains for the final crude tuple count, and all actual lattice, word, unit, physical-box and reconstruction arguments remain separate; the full original conjecture is not asserted here.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalRangeCutoffs.original_range_numeric_cutoffs`
