# Exponential Square Weights and Ternary Support

## Abstract

The two modulo-three support conjectures of OEIS A397242 hold in both directions.

The two conjectures in hanna2026a397242b concern the coefficients of A(x)=exp(x+Sum (n^2-1)a(n)x^n/n^2), with the sum over n>=2. All indices and exponents below are natural numbers. The function a takes integer values, and mod denotes integer remainder. The two powers in the residue-two statement are distinct because i<j.

The symbols a and d refer to the imported declarations `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a` and `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d`. The integral recurrence and normalization are `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d_recurrence` and `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a_eq`. Their connection to the exponential equation is established by `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.log_derivative_identity`, `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.coeff_M_rat`, and `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.generating_unique`. These give A(0)=1, X A'=M A, the exact rational coefficients of M=X L', and uniqueness with that coefficient shape.

**Theorem 1.1 (The complete coefficient classification).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) \bmod 3 = (\operatorname{if} ((\exists k: \mathbb{N}, (n + 2 = (3)^{k})) \lor (\exists k: \mathbb{N}, (n + 2 = (2) \cdot ((3)^{k})))) \operatorname{then} 1 \operatorname{else} (\operatorname{if} (\exists i: \mathbb{N}, (\exists j: \mathbb{N}, ((i < j) \land (n + 2 = (3)^{i} + (3)^{j})))) \operatorname{then} 2 \operatorname{else} 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.ternary_support_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work over ZMod(3). Split the imported recurrence into the three index classes. The series U(x)=Sum d(3m+1)x^m and V(x)=Sum d(3m+2)x^m satisfy U=1+xVU and V=U-xV^2, so V=1+x^2V^3. Set T=xV and F=xU. Then T=x+T^3, F=T+T^2, and F=x+x^2A modulo three. Frobenius and strong induction show that T has coefficient one precisely at powers of three. The identity F=x+x^2+F^3-xT^3 gives the three coefficient recursions for F. Dividing exponents by three proves the displayed classification, including the constant coefficient of A.

**Theorem 1.2 (The residue-one conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{a}\left(n\right) \bmod 3 = 1 \iff ((\exists k: \mathbb{N}, (n + 2 = (3)^{k})) \lor (\exists k: \mathbb{N}, (n + 2 = (2) \cdot ((3)^{k}))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_one` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397242-mod-three-powers` (proved) by `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_one`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397242-mod-three-powers","declaration_gid":"D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_one","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397242, o.g.f. A = exp(x + Sum (n^2-1) a(n) x^n / n^2)*. URL: <https://oeis.org/A397242>.

*Commentary.*

The classification gives remainder one exactly in its first branch. The other branches give remainders two and zero. This proves both directions of the first modulo-three conjecture in hanna2026a397242b.

**Theorem 1.3 (The residue-two conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{a}\left(n\right) \bmod 3 = 2 \iff (\exists i: \mathbb{N}, (\exists j: \mathbb{N}, ((i < j) \land (n + 2 = (3)^{i} + (3)^{j}))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_two` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397242-mod-three-sums` (proved) by `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_two`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397242-mod-three-sums","declaration_gid":"D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_two","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397242, o.g.f. A = exp(x + Sum (n^2-1) a(n) x^n / n^2)*. URL: <https://oeis.org/A397242>.

*Commentary.*

Ternary induction also proves that a sum of two distinct powers of three is neither a single power nor twice a power of three. The second branch of the classification therefore applies exactly to these sums. This proves both directions of the second modulo-three conjecture in hanna2026a397242b.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a_eq`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.coeff_M_rat`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d_recurrence`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.log_derivative_identity`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_one`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.hanna_conjecture_two`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.ternary_support_classification`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](ExponentialSquareWeightCatalanParity.md)
