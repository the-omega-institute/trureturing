# Capped Coupling Certificate Replay

## Abstract

Concrete capped-coupling certificates and corrupted-input rejection checks.

**Theorem 1.1 (A complete real interval from numerical evidence).**

$$\operatorname{RealQueryImage}\left(cappedMatrix, \operatorname{cappedRhs}\left(\frac{1}{2}, \frac{2}{3}, \frac{1}{3}\right), jointObjective\right)=\operatorname{Icc}\left(\frac{5}{12}, \frac{1}{2}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CheckedLinearImageExamples.capped_fixture_real_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RealQueryImage is the image of all real vectors x satisfying the cast rational inequalities under the cast rational objective. The coordinate order is 00,01,10,11 and jointObjective is (0,0,0,1). There are no hypotheses.

The eleven rows encode four nonnegative coordinates, total mass one in both directions, each marginal in both directions, and a disagreement cap. cappedRhs(p,q,delta) is (0,0,0,0,1,-1,p,-p,q,-q,delta).

The accepted lower witness is (1/4,1/4,1/12,5/12) and the upper witness is (1/3,1/6,0,1/2). Lower multipliers put 1/2 on each negative marginal row and the cap row; upper multipliers put one on the first positive marginal row and on the 10 nonnegativity row. capped_payload_accepted is proved by kernel reduction and is consumed by checked_real_query_image.

Four separate kernel-checked mutations reject a negated upper multiplier vector, a changed lower witness coordinate, a doubled objective coefficient, and a zero disagreement cap. The checker always receives the authoritative problem separately from the payload.

**Theorem 1.2 (An accepted Farkas certificate excludes real solutions).**

$$\neg\exists x:\operatorname{Fin}\left(4\right)\to \mathbb{R}, \operatorname{RealFeasible}\left(cappedMatrix, \operatorname{cappedRhs}\left(\frac{3}{4}, \frac{1}{4}, \frac{1}{4}\right), x\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CheckedLinearImageExamples.inconsistent_fixture_real_infeasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RealFeasible means every cast row inequality holds. The statement has no hypotheses. The weights are (0,2,0,0,0,0,0,1,1,0,1); their weighted columns vanish and the right-hand side is -1/4.

inconsistent_payload_accepted checks this raw data by kernel reduction. checked_infeasible then excludes every real solution. These examples certify four-cell systems; they do not assert a structural causal interpretation or coverage of all ternary responses.

## References

- Truth anchor: `D5/S0/Certificates/CheckedLinearImageExamples.capped_fixture_real_image`
- Truth anchor: `D5/S0/Certificates/CheckedLinearImageExamples.inconsistent_fixture_real_infeasible`
- Dependency: [D5/S0/Certificates/CheckedLinearImage](CheckedLinearImage.md)
