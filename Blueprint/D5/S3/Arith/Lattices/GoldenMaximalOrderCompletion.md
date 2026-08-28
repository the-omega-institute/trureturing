# Golden Maximal-Order Completion

## Abstract

The golden Hodge lattice completes to a stable full-rank lattice, while the sqrt-five order has index two in the golden integers.

**Theorem 1.1 (The golden completion is stable and the order defect is repaired at two).**

$$\begin{aligned}maximalOrderLattice = integerLattice + \operatorname{map}(integerLattice, goldenOperatorInt) \land\\\operatorname{IsFullRank}(maximalOrderLattice) \land\\integerLattice \subseteq maximalOrderLattice \land\\\operatorname{IsGoldenStable}(maximalOrderLattice) \land\\{\forall M, (integerLattice \subseteq M \land \operatorname{IsGoldenStable}(M)) \Rightarrow maximalOrderLattice \subseteq M} \land\\sqrtFiveOrder \subset GoldenInt \land\\\operatorname{relIndex}(sqrtFiveOrder, GoldenInt) = 2 \land\\\operatorname{discr}(GoldenNumberField) = 5 \land\\\operatorname{orderOf}(fiveCycleOnCompletion) = 5 \land\\\forall x: GoldenInt, \operatorname{goldenIntegerTwoAdicEmbedding}(2\cdot x): GoldenTwoAdicCompletion \in completedSqrtFiveOrder.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion.golden_maximal_order_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All ten displayed clauses are the ten conjuncts of the Lean theorem. The ambient GoldenSpace is the rational scalar extension of the ordered six-coordinate Lambda-squared A4 lattice from ExactDualLatticeFormula. The operator goldenOperatorInt is the integer-linear restriction of Phi=(I+J)/2 for that module's explicit Hodge matrix J.

The first five clauses state the lattice formula, full rank, containment, stability under every concrete GoldenInt element a+b*phi, and the corresponding leastness property. The leastness quantifier ranges over integral submodules of this same concrete GoldenSpace.

The next two clauses use sqrtFiveOrder, the GoldenInt elements whose phi coordinate is even. They state both strict inclusion in GoldenInt and relative additive index two. Thus the Scribe formula records the index of Z[sqrt(5)] in Z[phi], rather than substituting the separate index-two calculation for the completed Hodge lattice.

The final three clauses identify the number-field discriminant of the named golden field Q(sqrt(5)) as five, give exact order five for the explicit exterior-square five-cycle on the completed lattice, and place the image of twice every GoldenInt element in the image of sqrtFiveOrder inside the finite-place completion above two. No hypothesis, uniqueness claim, or stronger ring-of-integers identification is added here.

## References

- Truth anchor: `D5/S3/Arith/Lattices/GoldenMaximalOrderCompletion.golden_maximal_order_completion`
- Dependency: [D5/S0/Carrier/GoldenDiscriminant](../../../S0/Carrier/GoldenDiscriminant.md)
- Dependency: [D5/S0/Carrier/Ring](../../../S0/Carrier/Ring.md)
- Dependency: [D5/S3/Arith/Lattices/ExactDualLatticeFormula](ExactDualLatticeFormula.md)
