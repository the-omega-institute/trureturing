# Finite Genus-Zero Central-Moment Expansion

## Abstract

Finite genus-zero factors admit an exact central-moment expansion with remainder.

**Theorem 1.1 (Finite logarithmic sums have an exact moment expansion).**

$${\forall j\in s, 1+v_j \cdot w \neq 0} \Rightarrow \\{}\sum_{j\in s} \frac{m_j \cdot v_j}{1+v_j \cdot w} = \sum_{0 \leq n < K} {-1}^{n} \cdot {\sum_{j\in s} m_j \cdot v_j^{n+1}} \cdot w^{n} + \sum_{j\in s} \frac{m_j \cdot v_j \cdot {-v_j \cdot w}^{K}}{1+v_j \cdot w}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/FiniteGenusZeroMomentExpansion.centralLogSum_eq_momentExpansion_add_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be a finite index set, let v_j be complex nodes with natural multiplicities m_j, and fix a complex argument w. If every factor 1 + v_j w is nonzero, then the associated finite logarithmic sum equals its central-moment expansion through every order K plus the displayed exact geometric remainder. The case K = 0 is included: the empty moment sum vanishes and the remainder is the original sum.

The source atom states an infinite genus-zero canonical product and an infinite Taylor expansion. Those claims require convergence and order infrastructure that the atom does not supply. The deposited theorem therefore records the finite algebraic core without claiming analytic convergence; its explicit remainder retains the full finite content.

Six-route repository searches found no equivalent D5 declaration. The pinned library was also searched first and supplies the product logarithmic-derivative rule, the power rule, the finite geometric-sum identity, and finite-sum commutation. The proof applies those results directly and makes the nonzero denominator condition explicit.

## References

- Truth anchor: `D5/S3/Analytic/FiniteGenusZeroMomentExpansion.centralLogSum_eq_momentExpansion_add_remainder`
