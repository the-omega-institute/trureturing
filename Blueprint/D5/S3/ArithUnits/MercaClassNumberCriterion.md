# Actual Class Numbers and the Full Centered Criterion

## Abstract

Actual Class Numbers and the Full Centered Criterion

**Definition 1.1 (The exact signed class-number difference).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.delta`

*Formalization.* `D5/S3/ArithUnits/MercaClassNumberCriterion.delta` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Delta is the integer half of the genuine imaginary quadratic ideal class number minus m. The upstream equality proves that the half is exact.

**Theorem 1.2 (The signed congruence).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.delta_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.delta_congruence` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The actual Delta is congruent to k+t modulo four. The literal imaginary quarter sum counts nonresidues modulo two, and the universal quarter identity supplies the required congruence.

**Theorem 1.3 (Equality before sign).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.equality_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.equality_criterion` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Equal coordinate magnitudes are equivalent to the genuine relative class number being exactly k squared. Merely being a square is insufficient.

**Theorem 1.4 (The two sign branches).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.sign_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.sign_criterion` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Under equal magnitudes, Delta is two modulo four exactly when k=t and zero modulo four exactly when k=-t. Oddness of k distinguishes both cases.

**Theorem 1.5 (The full class-number centered criterion).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.centered_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.centered_criterion` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every distinct prime q, the literal centered sum on H is equivalent to chi(q)=1, or the actual quotient equals k squared with Delta two and chi(q)=-i, or the actual quotient equals k squared with Delta zero and chi(q)=i. Together with the existing CRT structure and generator theorem, this retains all admissible odd q including three, on either side of r.

**Theorem 1.6 (The actual fixed field survives conjugation).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.conjugate_invariants`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.conjugate_invariants` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Conjugation fixes K and its literal cyclotomic fixed field, hence the real subfield and genuine class numbers. The real coordinate is unchanged and the imaginary coordinate is negated, with the same actual norm identity.

**Theorem 1.7 (The conjugate centered branches).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.conjugate_centered_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.conjugate_centered_criterion` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

With chi-minus(2)=-i, the additional Delta-two centered branch uses chi-minus(q)=i and the Delta-zero branch uses -i. The same actual quotient, imaginary quadratic class number and Delta occur. The existing conjugate-coordinate theorem explicitly matches the ordered cosets K,2K,-K,-2K with values 1,-i,-1,i.

**Theorem 1.8 (The actual eligible source period).**

Lean statement: `D5/S3/ArithUnits/MercaClassNumberCriterion.generator_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaClassNumberCriterion.generator_criterion` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For each admissible odd q, an actual generator of H exists, has the source coprimality property, and its powers through one full order enumerate H once. Its literal least-positive residue sum therefore has the full class-number centered criterion, including admissible q=3.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Yao Xu/catalan-lean4 supplier notices remain intact. No novelty, priority, consent or publication claim is made.

The source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Kernel evidence and author exposition do not replace independent whole-result acceptance. Separate analytic density results of the MMZ preprint are outside this assignment.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.centered_criterion`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.conjugate_centered_criterion`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.conjugate_invariants`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.delta`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.delta_congruence`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.equality_criterion`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.generator_criterion`
- Truth anchor: `D5/S3/ArithUnits/MercaClassNumberCriterion.sign_criterion`
- Dependency: [D5/S3/Analytic/Zeta/MercaImaginaryClassNumber](../Analytic/Zeta/MercaImaginaryClassNumber.md)
- Dependency: [D5/S3/Analytic/Zeta/MercaRelativeClassNumber](../Analytic/Zeta/MercaRelativeClassNumber.md)
