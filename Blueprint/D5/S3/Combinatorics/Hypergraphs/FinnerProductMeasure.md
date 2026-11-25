# Finner's inequality on product probability spaces

## Abstract

Fractional incidence budgets control products of local measurable factors under one product probability law.

**Theorem 1.1 (Fractional hypergraph inequality).**

Lean statement: `D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure.finner_product_measure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure.finner_product_measure` (`✓ std3`). ∎

*Citation.* Helmut Finner (1992). *A Generalization of Holder's Inequality and Some Probability Inequalities*. DOI: [10.1214/aop/1176989534](https://doi.org/10.1214/aop/1176989534).

*Commentary.*

Let I and J be arbitrary finite types. For each coordinate i in I, let X_i be a measurable space and mu_i a probability measure. Write mu=Measure.pi(mu_i) on the dependent product of the X_i. For every factor j in J choose a set S_j of coordinates, a measurable function f_j from the full product to ENNReal, and a real weight w_j>=0. DependsOn(f_j,S_j) means that f_j takes equal values on any two points agreeing at all coordinates in S_j. Assume that, for every i, the sum of w_j over j with i in S_j is at most one.

Then the mu integral of the product over j of f_j(x) raised to w_j is at most the product over j of the mu integral of f_j, raised to w_j. Every integral uses this same product law, including the factor integrals on the right. There are no boundedness, finite alphabet, positive integral, disjoint support or global total-weight restrictions. Empty I, empty J and empty S_j are included. Values zero and infinity, zero weights, and their products use exactly ENNReal multiplication and real-power conventions, including zero times infinity equal to zero and any base to exponent zero equal to one.

For a finite coordinate set T, integrate only those coordinates, using lmarginal(mu,T). The induction estimate bounds the marginal of the original product by the product of the individual marginals raised to their weights. At an added coordinate i, the induction hypothesis first bounds the integrand. Only factors with i in S_j can vary during this integration; every other marginal is constant in i because its original factor depends only on S_j. Split these two finite products, extract the constant product by the full measurable ENNReal lintegral_mul_const identity, and apply Holder to the varying factors. A constant-one factor with weight one minus the incidence sum absorbs unused budget. The marginal insertion identity gives the next induction estimate. At T=I, lmarginal_univ identifies every term with the integral under Measure.pi(mu_i).

The proof directly reuses Mathlib's ENNReal.lintegral_mul_prod_norm_pow_le, Measurable.lmarginal, lmarginal_insert, lmarginal_update_of_mem, lmarginal_update_of_notMem, lmarginal_univ, and the measurable ENNReal real-power instance. The finite coordinate induction connects these suppliers to overlapping supports. The Library note identifies the classical theorem and distinguishes the directly read balanced finite-norm restatement from the probability weak-budget statement and extended endpoints proved here. No mathematical originality is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure.finner_product_measure`
