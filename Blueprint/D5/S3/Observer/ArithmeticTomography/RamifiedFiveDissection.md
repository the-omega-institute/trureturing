# Six-State Ramified Five-Dissection

## Abstract

The fixed Lambda-square A4 lattice realizes five residue states and one ramified jet state.

**Theorem 1.1 (Five residues acquire one additional isotropic residual channel).**

$$\operatorname{ncard}\left(\operatorname{range}\left(stateOf\right)\right) = \operatorname{card}\left(RamifiedFiveState\right) \land (\forall x \in ExteriorSquareA4, \operatorname{energyResidue}\left(x\right) \neq 0 \Rightarrow \operatorname{stateOf}\left(x\right) = \operatorname{ordinary}\left(\operatorname{ordinaryResidue}\left(x\right)\right)) \land \operatorname{rho5}\left(zeroWitness\right) = 0 \land \operatorname{rho5}\left(residualWitness\right) \neq 0 \land \operatorname{qR}\left(\operatorname{rho5}\left(residualWitness\right)\right) = 0 \land \operatorname{stateOf}\left(zeroWitness\right) \neq \operatorname{stateOf}\left(residualWitness\right) \land \neg \operatorname{firstOrderJetObservation}\left(ramificationResidual\right) \in \operatorname{range}\left((r \mapsto \operatorname{firstOrderJetObservation}\left(\operatorname{ordinary}\left(r\right)\right))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection.six_state_ramified_five_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ExteriorSquareA4 is the source's six-integer coordinate lattice with its displayed Gram matrix G. The boundary map uses the displayed fixed matrix R_5, and q_R uses the displayed matrix H. The first conjunct equates the cardinality of the actual stateOf image with the RamifiedFiveState carrier; ramified_state_card computes that carrier as the five ordinary constructors plus one residual constructor. For nonzero energy residue, stateOf returns that residue.

The theorem uses fixed lattice points, not caller-supplied witnesses. The zero point has zero R_5 boundary. The fixed residual point has a nonzero q_R-isotropic boundary, and stateOf assigns the two points different labels.

RamifiedFiveRoot carries the repository theorem 5 = (-1 + 2 phi)^2. Its class in the named first-order neighborhood GoldenInt/(5) is the residual jet. Ordinary state observations are zero in this quotient, while the final non-membership says the residual jet observation is not among them.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection.six_state_ramified_five_dissection`
