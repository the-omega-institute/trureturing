# Six-State Ramified Five-Dissection

## Abstract

Six observable states arise from five ordinary residues and one ramification residual.

**Theorem 1.1 (Five residues acquire one additional isotropic residual channel).**

$$6 = 5+ 1 \land (\forall x \in \operatorname{L}\left(D\right), \operatorname{energy}\left(D, x\right) \bmod 5 \neq 0 \Rightarrow \operatorname{stateOf}\left(D, x\right) = \operatorname{ordinary}\left(\operatorname{ordinaryResidue}\left(\operatorname{energy}\left(D, x\right)\right)\right)) \land \operatorname{rho5}\left(D, \operatorname{zeroWitness}\left(D\right)\right) = 0 \land \operatorname{rho5}\left(D, \operatorname{residualWitness}\left(D\right)\right) \neq 0 \land \operatorname{qR}\left(\operatorname{rho5}\left(D, \operatorname{residualWitness}\left(D\right)\right)\right) = 0 \land \operatorname{stateOf}\left(D, \operatorname{zeroWitness}\left(D\right)\right) \neq \operatorname{stateOf}\left(D, \operatorname{residualWitness}\left(D\right)\right) \land \neg ramificationResidual \in \operatorname{range}\left(ordinary\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection.six_state_ramified_five_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is built from five ordinary residue labels and a separate ramificationResidual label, so its cardinality is exactly 6 = 5 + 1. For every nonzero energy residue, the observer label is the residue n mod 5.

At zero residue, the supplied source witnesses distinguish a zero boundary from a nonzero boundary. The energy-boundary congruence forces the latter boundary to be q_R-isotropic, and the two labels are unequal.

The residual constructor is outside the range of ordinary labels. This is the extra first-order jet channel left by the ramified prime 5; the theorem assumes the source lattice data and does not replace it with an enumerated Fin carrier.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection.six_state_ramified_five_dissection`
