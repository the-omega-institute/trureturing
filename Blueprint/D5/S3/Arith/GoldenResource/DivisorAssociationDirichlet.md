# Dirichlet Energy of the Association Fibers

## Abstract

The finite association quotient has a genuine nonnegative Dirichlet energy whose kernel is exactly the q-measurable source data.

For a finite exponent box, form the finite set of ordered source pairs with equal observed position q. The pairwise energy sums the squared source-value differences over those pairs. It is a finite quadratic form, so its positivity is checked directly in Lean and does not use an RH equivalence.

**Definition 1.1 (Equal-observation source pairs).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.sameFiberPairs`

*Formalization.* `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.sameFiberPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordered pairs of box sources whose q-images agree.

**Definition 1.2 (Pairwise fiber Dirichlet energy).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy`

*Formalization.* `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum over equal-q pairs of (u(s)-u(t))².

**Theorem 1.3 (Energy positivity).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite-box fiber energy is nonnegative by termwise square positivity.

**Theorem 1.4 (Kernel characterization).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The energy vanishes exactly when the source function is constant on every q-fiber inside the box. This is the finite Fisher/Dirichlet kernel statement.

**Theorem 1.5 (q-measurable pullbacks are in the kernel).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_pullback_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_pullback_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any position function pulled back along q has zero fiber energy.

**Theorem 1.6 (Collision witness).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_pos_of_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_pos_of_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single equal-q pair with distinct source values forces strictly positive energy.

**Theorem 1.7 (5040 hidden-label defect).**

Lean statement: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_5040_hidden_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_5040_hidden_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the (4,2,1,1) exponent box corresponding to 5040, the fourth-exponent potential has positive energy because (1,0,0,1) and (2,0,1,0) share q but have different hidden labels. This is a finite exact witness, not an assertion of Robin's inequality or RH.

The construction is deliberately source-complete at the finite-box level: the kernel statement records precisely which information is lost by q. Connecting this quadratic form to the original Robin N_p, S_X or I_X requires an additional source lift and is not claimed by this module.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_5040_hidden_pos`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_eq_zero_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_nonneg`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_pos_of_collision`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.fiberEnergy_pullback_zero`
- Truth anchor: `D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.sameFiberPairs`
- Dependency: [D5/S3/Arith/GoldenResource/DivisorAssociationFiber](DivisorAssociationFiber.md)
