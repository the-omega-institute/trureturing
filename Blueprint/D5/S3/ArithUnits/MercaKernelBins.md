# Universal Identities for the Actual Kernel Bins

## Abstract

Universal Identities for the Actual Kernel Bins

**Definition 1.1 (The literal kernel-bin count).**

Lean statement: `D5/S3/ArithUnits/MercaKernelBins.binCount`

*Formalization.* `D5/S3/ArithUnits/MercaKernelBins.binCount` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

A_j is the integer cardinality of the native units u in the actual character kernel K with floor(4 val(u)/r)=j.

**Theorem 1.2 (The two universal bin identities).**

Lean statement: `D5/S3/ArithUnits/MercaKernelBins.bin_identities`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaKernelBins.bin_identities` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r greater than five congruent to five modulo eight, 5k=-3(A0-A3)-(A1-A2) and 5t=-(A0-A3)+3(A1-A2). The real parts of the literal quarter and half character sums are computed by kernel indicators and negation, then combined with the universal complex interval identities. The finite checker is not a premise.

Historical source credit: Haobo Ma and Wenlin Zhang, CC BY 4.0, including the unique verification ZIP; Joseph S. Farland/OEIS sign attribution, joint Ma-Merca-Zhang application and classical class-number sources remain credited. No novelty, priority, author-consent or publication claim. Source-owner audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629; these author proofs do not replace independent whole-result acceptance.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaKernelBins.binCount`
- Truth anchor: `D5/S3/ArithUnits/MercaKernelBins.bin_identities`
- Dependency: [D5/S3/ArithUnits/MercaQuarticMoments](MercaQuarticMoments.md)
