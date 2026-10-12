# RarePriorReferenceScalar

## Abstract

RarePriorReferenceScalar

The PH14 rational expressions e and f use the supplied exact constants. The PH17 polynomial isolates their unique nonnegative common root between 0.2333613 and 0.2333615. The scalar is e at that root. The statement proves the needed strict bound and makes no minimax or irrationality claim.

**Theorem 1.1 (exact reference scalar).**

$$\operatorname{lower} < \operatorname{aStar} \land \operatorname{aStar} < \operatorname{upper} \land \operatorname{rootPolynomial} \operatorname{aStar} = 0 \land ( \forall \operatorname{a} : \operatorname{Real} , 0 \leq \operatorname{a} \Rightarrow \operatorname{rootPolynomial} \operatorname{a} = 0 \Rightarrow \operatorname{a} = \operatorname{aStar} ) \land \operatorname{e} \operatorname{aStar} = \operatorname{f} \operatorname{aStar} \land 0 < \operatorname{tStar} \land \operatorname{tStar} < 1 / 10000$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorReferenceScalar.exact_reference_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorReferenceScalar.exact_reference_scalar`
