# A CRT law for actual square-displacement thresholds

## Abstract

The exact determinant histogram of two actual finite-group threshold sequences.

**Theorem 1.1 (Actual thresholds and their determinant histogram).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdDistribution.actual_square_displacement_threshold_distribution`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdDistribution.actual_square_displacement_threshold_distribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

For signed odd integers p,r>=5 and q_k=2k+3, the two sequences T_p(q_k) and T_r(q_k) are the unique first thresholds of the actual marked quotient-group return counts. The actual counts are Wa=(square_return_pair c q t).1 and Wq=(square_return_pair c q t).2, with c=p or c=r. Every state in the construction uses the original five crossing clauses: the lower guard, strict comparison before the crossing, the non-strict comparison at the crossing, strict comparison after it, and the late upper bound. The logarithmic lower and ceiling upper bounds are inherited from the completed actual-count bracket.

Write L=log(2), d=gcd(p,r), a=p/d and b=r/d. The theorem gives, for every integer z, the limiting frequency of r*T_p(q_k)-p*T_r(q_k). It is zero when d does not divide z or when j=z/d lies outside -a<j<b. On the support the mass is min(min(a,b),min(a+j,b-j))/(a*b), with all support and determinant arithmetic performed in the integers. The modulus-one case a=b=1 therefore gives mass one at z=0.

The proof first compares each actual threshold with the ideal ceiling ceil(p*q_k/(4L)). If the two differ, the strict lower bracket and the integer upper bracket force the fractional part of p*q_k/(4L) into the interval [0,A_p/q_k), where A_p=p/(4L)-1/2+1/(2p). For every positive delta this interval is eventually contained in [0,delta); a fixed initial prefix is retained in the counting bound. Irrational rotation interval sampling, with step p/(2L) and phase 3p/(4L), makes these exceptional indices have density zero. The same argument applies to r, and the two exceptional sets have density zero as a finite union. No eventual equality and no interpolation of the finite counts is used.

For the ideal determinant put y_k=d*q_k/(4L). Its rotation step d/(2L) is irrational. Split the circle into the a*b half-open cells [h/(a*b),(h+1)/(a*b)). Every cell has frequency 1/(a*b), and the irrational orbit never hits a rational endpoint. On the h-cell, the integer part of y_k cancels and the determinant is d*(b-a+(h mod a)-(h mod b)). The map h -> (h mod a,h mod b) is the finite cyclic action identified with ZMod(a*b) ~= ZMod(a) x ZMod(b) by the Chinese remainder equivalence.

Sending the two residues I,J to U=a-1-I and V=b-1-J changes the cell value to d*(V-U). The reference coordinates U,V are independent uniform residues in this finite Cartesian product. These are reference residues for the reflected CRT convolution; no independence of the original real rounding errors is asserted. Counting the fiber V-U=j gives max(0,min(a,b-j)-max(0,-j)), equal on the support to the displayed four-term minimum. The density-zero comparison transfers the ideal histogram to the actual finite-group thresholds.

The four Reg roles are the actual p-Wa, p-Wq, r-Wa and r-Wq count readouts on the whole signed odd family, with state (k,t) in Nat x Nat. The Law retains both full original count crossings, both logarithmic bounds, uniqueness among all original crossing thresholds in each fiber, and the all-z histogram; finite sample states witness only role variation and do not replace the infinite family law. The construction is a mathematical connection between quotient-group return counts, cyclic rotation, and the exact finite CRT convolution.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdDistribution.actual_square_displacement_threshold_distribution`
- Dependency: [D5/S1/Phase/IntervalSampling](../../S1/Phase/IntervalSampling.md)
- Dependency: [D5/S3/Constants/Irrationality/LogNaturalIrrationality](../Constants/Irrationality/LogNaturalIrrationality.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattySquareDisplacementLogTwoBracket](BajnokBeattySquareDisplacementLogTwoBracket.md)
