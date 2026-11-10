# The five Section 25.3 angle budgets

## Abstract

Exact strict angle budgets for the CFMP Section 25.3 certificate.

Define betaTwo=arccos(70/99), betaThree=arccos(49sqrt(6)/198), and thetaZero=arccos(31/33), thetaOne=arccos(25/sqrt(726)), thetaTwo=arccos(81/88).

**Theorem 1.1 (All five strict budgets).**

$$8\cdot betaTwo\left(\right) > 2\cdot \pi \land \left(6\cdot betaThree\left(\right)+ betaTwo\left(\right) > 2\cdot \pi \land \left(18\cdot thetaZero\left(\right) > 2\cdot \pi \land \left(11\cdot thetaOne\left(\right)+ 6\cdot thetaZero\left(\right) > 2\cdot \pi \land 9\cdot thetaTwo\left(\right)+ 7\cdot thetaOne\left(\right) > 2\cdot \pi\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/AngleBudgetCertificates.exact_angle_budget_certificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each arccosine is bounded below by a rational angle using a quarter-angle sine remainder estimate. The proof then combines the five rational lower bounds with the exact upper bound pi<3.1416.

The result is a numerical angle certificate for the prescribed CFMP local budgets. It does not construct edge lengths, prove a global cone metric, or establish the geometric realization bridge in later sections.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/AngleBudgetCertificates.exact_angle_budget_certificates`
