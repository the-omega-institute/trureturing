# Order-Three Complementary-Context Rigidity

## Abstract

A trace-zero order-three unitary cannot split nontrivially across two mutually unbiased diagonal contexts.

**Theorem 1.1 (An order-three unitary has only one nonzero context component).**

$$\operatorname{MutuallyUnbiasedOrthogonalRankOneContexts}(C, D, d) \land \operatorname{PositiveDimension}(d) \land \operatorname{ZeroSumCoefficients}(a, b)\\ \land \operatorname{UnitaryOrderThreeSpectralSum}(C, D, a, b) \Rightarrow\\\operatorname{AtLeastOneCoefficientFamilyVanishes}(a, b).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity.orderThree_complementary_contexts_no_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C and D be complete rank-one contexts in positive complex dimension d. Assume the within-context projectors are pairwise orthogonal and the existing overlap(C,D,i,j) equals 1/d. Let coefficient families a and b each have sum zero, and set A=sum_i a_i P_i, B=sum_j b_j Q_j. If S=A+B satisfies SS*=I and S^3=I, then every a_i is zero or every b_j is zero.

The proof reuses RankOneContext and its projection laws. Projecting SS*=I into C gives |a_i|^2=alpha=1-beta, where beta is the average of |b_j|^2. The order-three relation gives S^2=S*. Projecting this relation gives a_i^2+mu=conj(a_i), with mu the average of b_j^2. Summing squared moduli and using sum_i a_i=0 yields alpha^2=alpha+|mu|^2. Therefore alpha beta+|mu|^2=0; nonnegativity forces one coefficient family to vanish.

This is a conditional rigidity theorem for an actual matrix decomposition. It does not assume or prove a strict-X completion-affinity lower bound, does not classify common-unbiased roots, and does not exclude four MUBs globally. No rowwise collision threshold is used. A separate geometric adapter must supply the decomposition when consuming a saturated symmetry-plane budget.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity.orderThree_complementary_contexts_no_split`
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](RankOneContextCommutator.md)
