# The all-source native twisted current commutator

## Abstract

The all-source native twisted current commutator

The current on the complete original ordinary source carrier is LatticeHalfFockOriginalMixedIterate.sourceCurrent, itself the literal LatticeAllStateField.Y of originalFirstDescendant D h 0. Its coefficients are the original neutralMode combinations; no source mode is reconstructed from the desired twisted formula. All finite charged oscillator polynomials, arbitrary h and every signed integer half-mode are included. Only hu:IsUnit D.G.det is assumed.

**Theorem 1.1 (The all-source native twisted current commutator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateCurrentCommutator.actual_current_Ytw_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateCurrentCommutator.actual_current_Ytw_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The exact coefficient law is [currentCombination h j, Ytw(source).coeff E] = finsum k:Nat, Ring.choose(j+1/2,k) times Ytw(sourceCurrent(h)[[k]] source).coeff(E-(2*j+1)+2*k). binomial_product identifies Ring.choose with the descending finite product divided by k factorial. The doubled-cover exponent shift and physical half-frequency are literal.

sourceCurrent_upper_truncation is proved on the finite sum of actual charged polynomials with the original polynomialFrequencyBound. sourceCurrent_nat_support and current_Ytw_rhs_support bound the actual source and RHS supports by range(vectorFrequencyBound(source)+1). The final current sum uses that common bound for every colour, including the empty colour sum at rank zero. The proof is not a charged-ground extrapolation.

The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.

This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateCurrentCommutator.actual_current_Ytw_commutator`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedCurrentAction](LatticeHalfFockCorrectedCurrentAction.md)
