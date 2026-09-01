# Exact Rational Farkas Certificates

## Abstract

Exact nonnegative rational dual weights certify infeasibility of finite linear inequality systems.

**Theorem 1.1 (A negative rational dual combination excludes every primal solution).**

$$\forall A, b, \operatorname{Certificate}(A, b) \Rightarrow \neg \exists x, \operatorname{LinearFeasible}(A, b, x).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalFarkas.infeasible_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The primal system consists of finitely many exact rational inequalities A x less than or equal to b.

A certificate assigns a nonnegative rational weight to every row, annihilates every variable coefficient after weighted summation, and makes the weighted right-hand side strictly negative.

Any feasible point would make the same weighted right-hand side nonnegative. Lean checks the finite sum rearrangement and contradiction using exact ordered-field arithmetic.

## References

- Truth anchor: `D5/S0/Certificates/RationalFarkas.infeasible_of_certificate`
