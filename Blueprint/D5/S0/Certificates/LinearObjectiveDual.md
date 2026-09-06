# Exact Rational Linear Objective Certificates

## Abstract

Exact rational primal and dual witnesses certify finite linear objective bounds and endpoint optimality.

A feasible point satisfies a finite rational system A x less than or equal to b. A linear query is evaluated by an exact finite rational sum.

An upper certificate is a nonnegative combination of constraint rows that represents the objective coefficients and whose weighted right-hand side is below the proposed upper value. A lower certificate applies the same construction to the negated objective.

Weak duality proves universal validity. A feasible primal point with the same objective value upgrades validity to exact endpoint optimality. External optimization software may propose both witnesses, while Lean checks every coefficient, sign, sum, and equality.

**Theorem 1.1 (A rational upper dual certificate proves a universal bound).**

$$\forall A, b, c, u, \operatorname{UpperBoundCertificate}(A, b, c, u) \Rightarrow \forall x, \operatorname{LinearFeasible}(A, b, x) \Rightarrow \operatorname{linearObjective}(c, x) \le u.$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LinearObjectiveDual.upper_bound_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every feasible primal point, the nonnegative weighted constraint sum equals the objective and is bounded by the certificate right-hand side.

**Theorem 1.2 (A rational lower dual certificate proves a universal bound).**

$$\forall A, b, c, l, \operatorname{LowerBoundCertificate}(A, b, c, l) \Rightarrow \forall x, \operatorname{LinearFeasible}(A, b, x) \Rightarrow l \le \operatorname{linearObjective}(c, x).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LinearObjectiveDual.lower_bound_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate represents the negated objective, so exact weak duality yields the claimed lower bound after reversing the sign.

**Theorem 1.3 (Matching rational dual and primal witnesses certify an exact lower endpoint).**

$$\forall A, b, c, l, \operatorname{LowerBoundCertificate}(A, b, c, l) \Rightarrow \operatorname{PrimalWitness}(A, b, c, l) \Rightarrow \operatorname{IsExactLowerBound}(A, b, c, l).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LinearObjectiveDual.exact_lower_bound_of_certificate_and_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual witness supplies universal validity and the primal witness supplies attainment at the same exact rational value.

**Theorem 1.4 (Matching rational dual and primal witnesses certify an exact upper endpoint).**

$$\forall A, b, c, u, \operatorname{UpperBoundCertificate}(A, b, c, u) \Rightarrow \operatorname{PrimalWitness}(A, b, c, u) \Rightarrow \operatorname{IsExactUpperBound}(A, b, c, u).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LinearObjectiveDual.exact_upper_bound_of_certificate_and_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem packages the proof obligation required for certified linear-program endpoint sharpness.

## References

- Truth anchor: `D5/S0/Certificates/LinearObjectiveDual.exact_lower_bound_of_certificate_and_witness`
- Truth anchor: `D5/S0/Certificates/LinearObjectiveDual.exact_upper_bound_of_certificate_and_witness`
- Truth anchor: `D5/S0/Certificates/LinearObjectiveDual.lower_bound_of_certificate`
- Truth anchor: `D5/S0/Certificates/LinearObjectiveDual.upper_bound_of_certificate`
- Dependency: [D5/S0/Certificates/RationalFarkas](RationalFarkas.md)
