# Exact Value of c1

## Abstract

The c1 constant has two exact golden forms and the stated eight-decimal approximation.

**Theorem 1.1 (The c1 constant has its exact golden forms).**

$$c_{1} = 2\sqrt{5}T_{0} + E \land\\c_{1} = \frac{7(1-\sqrt{5})}{24} \land\\c_{1} = -\frac{7}{12\varphi} \land\\\lvert c_{1} - (-\frac{36051983}{100000000}) \rvert < \frac{1}{200000000}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/COneExactValue.c_one_exact_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here T0 is the deposited exact Sturmian-Dirichlet value (27 - 13 sqrt(5)) / 24, E is the canonical elementary shell (137 - 61 sqrt(5)) / 24, and phi is Mathlib's golden ratio. Thus c1 is tied to the repository's authoritative exact definitions, not to the older rational T0 reference center in the values catalog.

Substitution and the identity sqrt(5)^2 = 5 give c1 = 7(1 - sqrt(5))/24. Rationalizing the golden-ratio denominator gives -7/(12 phi). Rational lower and upper bounds for sqrt(5) then show that the exact value is within 1/200000000 of -0.36051983, certifying every printed decimal place.

A checked negative control changes the exact numerator from seven to eight and proves that the resulting equality is false. The source table records this constant across rounds 144 through 178 and notes its four-revision history; those are provenance metadata rather than additional mathematical conjuncts.

## References

- Truth anchor: `D5/S3/Constants/COneExactValue.c_one_exact_value`
- Dependency: [D5/S3/Constants/SturmianDirichletValue](SturmianDirichletValue.md)
