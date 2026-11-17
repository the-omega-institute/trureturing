# The actual long-chart bad-degree average

## Abstract

Actual long reduced charts supply their heights, and their derivative defects have the original physical parameter average.

**Theorem 1.1 (Derive the coordinate heights from the actual reduced basis).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

For each epsilon>0 one positive C works for all primes p and actual reduced index-p-cubed and index-p-squared bases of the same original lattice parameters t,w and literal box X,Y. The first basis is long: p^6<H^2*Q(R), with positive H and H^2=XY. The original middle parameter lies in the box, the actual anchor satisfies physical(q)=(-w,-t), the basis first coordinate and original middle parameters are units modulo p^3, and the original right side 1+a1*a2*t*w is a unit. Every actual retained endpoint pair obeys the original word, has unit first physical coordinates, and lies in the literal box. Assuming 2X,2Y<p^3 and the three stated numerical cutoffs, its actual maximum derivative-zero degree is at most C*p^epsilon*(1+6H/(p*sqrt(Q(R2)))).

Take sigma=sqrt(Q(R)) from the actual long reduced basis and define J1=8H/sigma and J2=4H*sigma/p^3. The existing reduced-basis coordinate bound proves the anchor and all endpoint height inputs. The long-scale theorem proves J2<=J1, J2>2 and J1*J2=32XY/p^3. Thus no height supplier is assumed. Consume actual_record_bad_degree_subpower with these actual inputs. The explicit inequalities (32XY/p^3)^5<=M^5*p^3, (10368*3^9)^5*M^35<p^4 and (24*(8*18)^4)^5*M^40<p remain hypotheses; they have not been discharged over the final original range.

**Theorem 1.2 (Average the actual maximum derivative defects).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_average`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexandru Pascadi (2026). *Non-abelian amplification and bilinear forms with Kloosterman sums*. DOI: [10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0). URL: <https://arxiv.org/abs/2511.08445v2>.

*Commentary.*

Let A=XY. Under 1<=X<=Y, 2Y<p^3, A<2p^4, positive H with H^2=A and H>=p, and the same three numerical cutoffs, let s be any finite set of actual original unit middle parameters in the literal rectangle. An actual reduced long index-p-cubed basis matching R,V is required only at members of s. Keep the actual anchor, original coefficient units, unit basis first coordinate, original word, endpoint units and literal endpoint boxes, and the unit original right side at every such parameter. Then the sum of actualRecordBadDegree over s is at most C*p^epsilon*[A+(A/p)*(1+log(2p)/log(2))+A^2/p^4], with one constant chosen before p and all chart data.

Map the original units to the prime-square quotient and choose a genuine reduced prime-square basis only at each parameter in s, defining the unused value outside s to be zero. The preceding long-chart theorem bounds each actual degree by its prime-square shortest-vector weight. Dominate 1+6H/(p*sigma) by six times 1+H/(p*sigma), then apply the existing actual_physical_weight_average to the same finite set of original parameters. There is no count, injection, height or weight estimate supplied as a hypothesis, and no impossible globally quantified basis witness at the zero parameter.

These are actual-chart bounds used to remove the derivative-defect term in the global retained count. The source problem and original numerical cutoffs are attributed to Pascadi. The numerical cutoffs and reconstruction of all original rows still require their own arguments; this module does not assert the full original conjecture or official acceptance.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_average`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiOriginalBadDegreeAverage.actual_long_bad_degree_subpower`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalBadDegree](PascadiOriginalBadDegree.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage](PascadiOriginalWeightAverage.md)
