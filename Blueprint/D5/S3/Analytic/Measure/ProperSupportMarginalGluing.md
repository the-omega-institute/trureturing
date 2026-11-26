# Gluing common profiles from coordinate marginals

## Abstract

Normalized factorizations of deleted-coordinate marginals determine one common factorization of all proper-support rows.

**Theorem 1.1 (Proper-support marginal gluing).**

Lean statement: `D5/S3/Analytic/Measure/ProperSupportMarginalGluing.exists_common_profiles_of_deleted_marginal_factorizations`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Measure/ProperSupportMarginalGluing.exists_common_profiles_of_deleted_marginal_factorizations` (`✓ std3`). ∎

*Citation.* Helmut Finner (1992). *A Generalization of Holder's Inequality and Some Probability Inequalities*. DOI: [10.1214/aop/1176989534](https://doi.org/10.1214/aop/1176989534).

*Commentary.*

Let I be an arbitrary finite type and J any type, with X_i arbitrary measurable spaces, and mu_i probability measures. Write mu for their actual dependent product law. Fix an active finite coordinate set A and finite supports S_j contained in A, with S_j different from A for every j. Let f_j be measurable ENNReal functions on the full product that depend only on S_j. Their original masses m_j=integral_mu(f_j) are positive and finite.

For every k in A, suppose there is a measurable family g_i^(k) on X_i, each of integral one under mu_i, such that, for every j, the marginal obtained by integrating f_j over coordinate k equals m_j times the product of g_i^(k)(x_i) over i in S_j with k removed, mu-almost everywhere. The different k may use different families.

Then there exists one measurable family h_i, each with integral_mu_i h_i equal to one, such that every original row f_j equals m_j times the product of the same h_i(x_i) over S_j, mu-almost everywhere. No coordinate coverage, incidence weights, positive conditional masses, finite alphabets, topologies or countable-generation assumptions are imposed. Empty supports and index types are retained whenever the displayed hypotheses hold. If J is infinite, each row may have its own exceptional null set. Zeros on positive-measure sets and infinite values on null sets are allowed.

First normalize f_j by its positive finite original mass. For each coordinate occurring in some support, choose an incident row and take its one-coordinate marginal, integrating all other coordinates. Evaluate that marginal at a fixed anchor with this coordinate inserted. Marginal insertion gives a unit integral. An unused coordinate receives the constant profile one.

To recover row j, choose k in A outside S_j. Its k-marginal is pointwise the original normalized row. For each i in S_j, compare the chosen incident row with its k-deleted factorization. Integrate every coordinate except i. Measurable marginal integration preserves the almost-everywhere equality; unit coordinate integrals leave exactly g_i^(k)(x_i). Since k differs from i, the repeated integration over k is absorbed. Thus every selected h_i agrees with g_i^(k) under the original product law. A finite intersection of these equalities reconstructs row j. Multiplication by m_j restores the original normalization.

Bennett and Oh, Section 2.1, use this proper-support assembly within an induction for Finner stability. The statement here is the exact marginal gluing implication for measurable ENNReal factors. It assumes the concrete deleted-marginal factorizations. Finner saturation alone is not a hypothesis from which this declaration derives those factorizations. The full balanced Finner equality classification additionally requires their derivation by dimension induction and a treatment of rows with full active support.

## References

- Truth anchor: `D5/S3/Analytic/Measure/ProperSupportMarginalGluing.exists_common_profiles_of_deleted_marginal_factorizations`
- Dependency: [D5/S3/Analytic/Measure/ProductSupportIntersection](ProductSupportIntersection.md)
- Dependency: [D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure](../../Combinatorics/Hypergraphs/FinnerProductMeasure.md)
