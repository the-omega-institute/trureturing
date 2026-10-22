# Finite Signed Half-Current Cuts

## Abstract

Finite Signed Half-Current Cuts.

Write J(h,j) for the actual finite colour combination of tensorCurrent, beta for B(h,a), and V(E) for chargedCoefficient. R(E,q) uses J(h,j)V(E+2j+3) when j<q and V(E+2j+3)J(h,j) otherwise. Current mode j+1/2 has cover exponent -2j-3. The physical normal cut is j<0; the ordinary cover-coordinate normalMinusOne split is not substituted.

**Theorem 1.1 (Finite integer support before summation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutSummand_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutSummand_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every actual tensor vector, the charged field supplies a lower exponent bound and current truncation supplies a uniform upper current bound. Support lies in the finite integer interval from min(q,min(0,L-E-3)) to max(q,cutoff). This includes negative cuts and empty branch intervals, with no occupation restriction. The arbitrary tensor lower bound comes from the already constructed charged field.

**Theorem 1.2 (Exact Ward increment at one cut).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The two finite cut supports admit a common finite union. Finsum subtraction distributes only after both supports are proved finite. All differing summands vanish except j=q; the existing all-integer charged_tensor_current_ward, summed over colours, gives beta times V(E+2).

**Theorem 1.3 (Universal signed Ward telescope).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_telescope`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_telescope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Integer induction uses the forward Ward step for nonnegative cuts and solves the same exact step backwards for negative cuts. It proves R(E,q)=R(E,0)+q*beta times V(E+2), including q=0. The pointwise finite sums form a genuine complex-linear endomorphism on ActualTensor; no End-valued infinite support assertion is made.

**Theorem 1.4 (Finite creation-side Nat support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.leftTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.leftTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The injective substitution j=q-1-k pulls back the proved cut support. Its charged exponent is E+2q+1-2k. This branch is individually finite on every actual tensor state.

**Theorem 1.5 (Finite annihilation-side Nat support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.rightTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.rightTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The injective substitution j=q+k pulls back the proved cut support. Its charged exponent is E+2q+3+2k. This branch is individually finite on every actual tensor state.

**Theorem 1.6 (Two exact Nat reindexes).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_nat_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_nat_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The ranges of q-1-k and q+k are respectively the strict lower cut and closed upper cut. Split the original finite-support integer sum into these two indicators and use injective range reindexing. The integer inequalities and toNat inverses are proved for every signed cut.

**Theorem 1.7 (Identification with the frozen physical constructor).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_zero_normal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_zero_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At q=0, the two Nat sums are exactly the existing order-zero negativeTerm and positiveTerm. Their individual finite-support proofs justify commuting the finite colour sum and each finsum, so R(E,0) is precisely the existing normalInsertion coefficient.

**Theorem 1.8 (Literal Ytw coefficient uses the physical split).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual first-descendant coefficient equals R(E,0) minus beta/2 times V(E+2). The equality consumes the genuine Corr/Ytw coefficient theorem and the proved normal constructor identification; it is not a definition of a descendant field.

**Theorem 1.9 (Every signed cut gives the mixed product).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_mixed_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_mixed_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Add (q+1/2)*beta times V(E+2) to the actual Ytw coefficient of the literal original descendant. The proved signed telescope identifies this with the two individually finite Nat products. This feeds the literal original source-current specialization, rather than assuming twisted Jacobi.

All statements use arbitrary LatticeData, IsUnit G.det, finite colour weights, charge, integer exponents and cuts, and ActualTensor vectors. No positivity, rank restriction, charge restriction or module-law premise is added. The Reg mirror attempts the source telescope with exact dependent parameters and typed four-slot obligations; completed source admission is not claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_nat_reindex`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_step`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_telescope`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutProduct_zero_normal`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.cutSummand_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.leftTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.native_first_descendant_mixed_iterate`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendantCuts.rightTerm_finite`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant](LatticeHalfFockFirstDescendant.md)
