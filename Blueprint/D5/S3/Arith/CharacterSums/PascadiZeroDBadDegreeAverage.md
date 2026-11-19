# The original selected zero Dixon bad-degree average

## Abstract

The actual maximum bad-partner degrees on a selected zero Dixon middle stratum have the full finite physical-weight average under sixth-height separation.

**Theorem 1.1 (Average the actual maxima at sixth height).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage.actual_long_bad_degree_average_zero_dixon`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage.actual_long_bad_degree_average_zero_dixon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Let A=XY and C6=max(6804,24*(8*18)^4)=10319560704. For every epsilon>0 there is a positive constant C_epsilon, chosen before p and all original data, with the following property. Let p be prime, 1<=X<=Y, 2Y<p^3, A<2p^4, H>0, H^2=A and p<=H. Let a1,a2 be units modulo p^3, s a finite set of middle coordinates wt=(w,t) in the literal box, q the coordinate anchors, RV the basis pairs, and E the actual endpoint families. At each wt in s a genuine reduced index-p-cubed middle basis has precisely the pair RV(wt), physical(q(wt))=-wt, and p^6<A*weightedSq(X,Y,R). The first coordinate of R, both middle coordinates, and 1+a1*a2*t*w are units modulo p^3. Every e in E(wt) satisfies the original WordSolution, both endpoint first physical coordinates are units, and both physical endpoints lie in the literal box.

Define actualTripleDixon(q,base,e,e') by applying the existing Dixon residual to the three actual coefficient rows of base,e,e'. Its five columns are coeffL(q,-), coeffM(q,-), coeffQ, coeffR and coeffS. For each wt in s with E(wt) nonempty, require one base in E(wt) whose actual bad-partner cardinality equals actualRecordBadDegree. Filter its actual derivative-zero bad partners to S1 by requiring the associated pencil to have nonzero reduction modulo p. The selected stratum condition says actualTripleDixon(q,base,e,e')=0 for every e,e' in S1. It imposes no Dixon condition on the zero-reduction branch, other baselines or all endpoints. Empty E is included and has maximum degree zero.

If C6*(32*A/p^3)^6<p^5, the full sum over wt in s of actualRecordBadDegree(p,q(wt),R(wt),V(wt),E(wt)) is at most C_epsilon*p^epsilon*(A+(A/p)*(1+log(2p)/log(2))+A^2/p^4). The sum retains every member of s and every endpoint family. There is no additional 3Y<p^2 restriction.

For the selected baseline, adjoin its actual coefficient row to the nonzero-reduction bad partners. The original word gives the common p^3 root divisibility at the physical beta, and bad-partner membership gives derivative divisibility by p. Literal coordinate bounds give coefficient height eighteen, separately from the physical H. The actual zero Dixon singular cover constructs at most three primitive irreducible factors, all relevant to the modular root. The existing actual fixed-factor value-pair bound and singular-factor endpoint count give the nonzero-reduction count with the original physical shortest-vector weight. No nonalignment, baseline resultant unit, rank-three hypothesis, factor cover or cardinality supplier is assumed.

For I>=J>=1, the sixth-height gap implies 18<p, 8IJ<p, 6I^3<p^3 and I<=p, using C6>=18^5 and C6>=8^6. These are exactly the numerical inputs of the existing zero-reduction count, including aligned and degenerate baselines. Partition the actual bad partners into zero and nonzero reductions, pay the physical weight once, and use the selected equality with the actual maximum. No factor equal to the number of baselines is introduced.

The genuine long basis supplies sigma=sqrt(weightedSq(X,Y,R)), J1=8H/sigma, J2=4H*sigma/p^3, J2<=J1, J2>2 and J1*J2=32A/p^3. Its coordinate theorem supplies the anchor and all endpoint bounds. Reduce the middle units modulo p^2 and choose shortest reduced prime-square bases only at members of s. The pointwise maximum bound is then averaged by actual_physical_weight_average on that same finite middle set. The final multiplier is 12288 times the pointwise constant. This proves the stated selected-stratum average; it supplies no total-count exponent or arbitrary-modulus conclusion.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiZeroDBadDegreeAverage.actual_long_bad_degree_average_zero_dixon`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners](PascadiOriginalAlignedPartners.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalGoodRecordMoment](PascadiOriginalGoodRecordMoment.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage](PascadiOriginalWeightAverage.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSeventhSingularCount](PascadiSeventhSingularCount.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiZeroDCover](PascadiZeroDCover.md)
