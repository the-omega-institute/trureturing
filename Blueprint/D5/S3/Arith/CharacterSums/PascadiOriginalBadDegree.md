# The actual bad degree is bounded

## Abstract

The maximum cardinality of the actual derivative-zero fibers satisfies the original weighted subpower bound.

For the actual finite retained endpoint chart E, actualRecordBadPartners(E,base) filters E by vanishing of the actual pencil derivative at the genuine physical ratio V1/R1 modulo p. The natural number actualRecordBadDegree is the finite maximum of these cardinalities over actual baselines in E, with value zero for the empty chart. It is an intrinsic count, not a supplied degree estimate.

**Theorem 1.1 (Consume the complete partner bound for the actual maximum).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegree.actual_record_bad_degree_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegree.actual_record_bad_degree_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For every epsilon>0 a single positive C bounds actualRecordBadDegree by C*p^epsilon*(1+6H/(p*sigma)). Fix the original prime p, units a1,a2,t,w, actual B modulo p^3 and reduced B2 modulo p^2, positive X,Y,H with H^2=XY, and sigma=sqrt((Y/X)B2.R1^2+(X/Y)B2.R2^2). Retain the anchor identity, original shifted unit and basis unit. Every member of E satisfies the original word, the actual endpoint units, J1,J2 coordinate bounds and literal physical rectangle with 2X,2Y<p^3. Assume 1<=J2<=J1 and the same cap and two explicit large-parameter cutoffs as the complete derivative-zero partner theorem. No global family of bases outside the actual parameter domain is required.

The empty chart has degree zero. In a nonempty chart choose an actual baseline attaining the finite maximum; its original word, physical units and coordinate bounds follow from its membership in E. The actual derivative-zero filter inherits all original partner hypotheses. The inverse of the original basis unit agrees with the total ZMod inverse used in recordBeta, so the derivative test is exactly the one in the complete actual partner theorem. Apply that theorem to this literal filtered set to bound the maximum.

This supplies the actual defect term used by the good-record second-moment argument. It is not itself the final average over original parameters and does not close the full Pascadi six-variable conjecture. The original problem and pencil are attributed to Pascadi.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegree.actual_record_bad_degree_subpower`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalDerivativePartners](PascadiOriginalDerivativePartners.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment](PascadiOriginalGoodRecordMoment.md)
