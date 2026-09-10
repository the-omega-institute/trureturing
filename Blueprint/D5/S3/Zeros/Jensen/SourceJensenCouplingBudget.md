# Source Jensen Coupling Budget

## Abstract

The exact source coupling sum is the fourth cumulant budget.

**Theorem 1.1 (The coefficient and cumulant sum).**

$$\begin{aligned}\forall n\in \mathbb{N},\quad \forall \lambda:\operatorname{Fin}(n+1)\to \mathbb{R},\\a_{0}=1\land \operatorname{Injective}(\lambda)\land (\forall i,0< \lambda_{i}\land q_{d-1}(\lambda_{i})=0)\implies\\(\forall i,q_{d}''(t_{i})\neq 0)\\\land \sum_{i}\mathrm{eta}_{i}=\frac{d-1}{d^{2}}(a_{1}^{2}-2a_{2})\\\land \sum_{i}\mathrm{eta}_{i}=-\frac{d-1}{12d^{2}}\mathrm{chi}_{4}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenCouplingBudget.source_jensen_coupling_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here d=n+2, a_k=sourceThetaCoefficient k, and q_d is the same real sourceQ as in SourceJensenIntegralExtension. All i range over Fin(n+1), with exactly d-1 terms. The hypotheses are source normalization a_0=1 and the preceding polynomial's distinct strictly positive real roots lambda_i. Set t_i=((d-1)/d)lambda_i and eta_i=sourceCoupling d t_i, exactly the couplings used in SourceJensenPositiveExtension.

$t_{i}=\frac{d-1}{d}\lambda_{i},\quad \mathrm{eta}_{i}=\frac{-dq_{d}(t_{i})}{q_{d}''(t_{i})},\quad \mathrm{chi}_{4}=m_{4}-3m_{2}^{2}$

The stored sourceThetaMoment k is the moment of order 2k: m_2=sourceThetaMoment 1 and m_4=sourceThetaMoment 2. Thus chi_4 is m_4-3m_2^2. Both displayed equalities are explicit conclusions, as is the nonzero second derivative at every node. This algebraic identity requires no assumption that the couplings are nonnegative.

The proof specializes Lagrange.coeff_eq_sum to R=q-d^(-1)Xq'+(a_1/d^2)q'. Its degree, node values, and coefficient are polynomial normalization; B1.1 supplies the critical nodes. The fourth-cumulant equality uses only a_1=m_2/2, a_2=m_4/24 and ring normalization. No root estimate, induction, or finite instance is added.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenCouplingBudget.source_jensen_coupling_budget`
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenPositiveExtension](SourceJensenPositiveExtension.md)
