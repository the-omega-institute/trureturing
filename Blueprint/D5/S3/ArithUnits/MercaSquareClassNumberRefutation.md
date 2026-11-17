# The Historical Square-but-Unequal Counterexample

## Abstract

The Historical Square-but-Unequal Counterexample

**Definition 1.1 (The square-only replacement).**

Lean statement: `D5/S3/ArithUnits/MercaSquareClassNumberRefutation.claim`

*Formalization.* `D5/S3/ArithUnits/MercaSquareClassNumberRefutation.claim` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The refuted claim says that every prime r greater than five congruent to five modulo eight with a square genuine relative class number has equal absolute quartic coordinates. This is a tempting weakening, not the historical theorem.

**Theorem 1.2 (The actual r181 refutation).**

Lean statement: `D5/S3/ArithUnits/MercaSquareClassNumberRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaSquareClassNumberRefutation.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For r=181, the actual normalized character kernel is identified with the 45 distinct powers of two with exponents 4j. Kernel-checked finite sums are (3439,3982,4706,4163), giving k=-7 and t=-1. The proved universal actual-object norm theorem gives the genuine relative class number 25, and the signed quarter theorem gives the genuine imaginary class number h(-724)=10. Thus square alone does not force equal magnitudes. This refutation does not claim that the finite checker independently computes ideal class groups.

Historical source: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Retained Yao Xu/catalan-lean4 supplier notices. No novelty, priority, author-consent or publication claim.

The original 313-prime census, first-ten signs and r13 reduced-form example remain finite source evidence: 24 equal-coordinate cases versus 49 square relative-class-number cases through 10000. No density or universal classification follows from it. Source-owner audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629; author evidence is distinct from independent acceptance.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaSquareClassNumberRefutation.claim`
- Truth anchor: `D5/S3/ArithUnits/MercaSquareClassNumberRefutation.result`
- Dependency: [D5/S3/ArithUnits/MercaClassNumberCriterion](MercaClassNumberCriterion.md)
