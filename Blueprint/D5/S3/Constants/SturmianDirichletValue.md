# Sturmian-Dirichlet Value

## Abstract

The exact Sturmian-Dirichlet value is a fixed affine combination of the golden ratio and the twisted cotangent constant.

**Theorem 1.1 (The Sturmian-Dirichlet value has its exact golden-ratio form).**

$$T_{0} = \frac{27 - 13\sqrt{5}}{24} = \varphi - \frac{7}{4} + C_{\varphi}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/SturmianDirichletValue.sturmian_dirichlet_value_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define T0 as (27 - 13 sqrt(5)) / 24 and C_phi as (57 - 25 sqrt(5)) / 24. Mathlib supplies the golden ratio phi = (1 + sqrt(5)) / 2. Substitution and normalization over the reals prove T0 = phi - 7/4 + C_phi exactly.

The decimal printed in the source table is an explanatory approximation, not a second exact claim. A checked negative control changes 57 to 58 and proves that the resulting equality fails.

## References

- Truth anchor: `D5/S3/Constants/SturmianDirichletValue.sturmian_dirichlet_value_eq`
