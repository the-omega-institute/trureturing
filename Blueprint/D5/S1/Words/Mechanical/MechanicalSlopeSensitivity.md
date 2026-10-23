# Mechanical Slope Sensitivity

## Abstract

Finite numerical slope precision has an exact local cost in actual binary observations.

**Definition 1.1 (Actual word disagreement phases).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.slopeDisagreement`

*Formalization.* `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.slopeDisagreement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the subset of the unit phase interval at which the existing lowerMechanicalWord observations disagree at some time before n. The slope is perturbed while the initial phase and the convention for floor boundaries are held fixed.

**Theorem 1.2 (Quantified chamber, exact measure, and correlated bit changes).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.local_slope_disagreement_law`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.local_slope_disagreement_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every irrational slope strictly between zero and one and every finite horizon, the proof constructs a positive radius using actual distances between its cuts and from the relevant endpoints. For any common lower bound g on one minus the slope, each cut's distance from zero, and all pairwise cut distances, the constructed radius is at least g/(2*(n+1)). Every nonnegative perturbation inside it gives an exact disagreement set: the disjoint swept intervals [1-fract(k*alpha)-k*delta,1-fract(k*alpha)), for k=1 through n. Their Lebesgue measure is delta*n*(n+1)/2. On the k-th interval the actual letter changes by +1 at time k-1, by -1 at time k when that position is observed, and by zero elsewhere. Irrationality, floor carries, interval separation, and measure additivity are derived in the live proof; no noise-region or measure certificate is assumed. The approximating slope need not be irrational. This is a local parameter-sensitivity theorem, not a global error law or an independent bit-noise model.

Apply this law to the Hamming count of the actual words as follows. Fix irrational alpha with 0 < alpha < 1 and a natural horizon n >= 1. Take the same radius supplied by local_slope_disagreement_law at n: it is positive, alpha+radius < 1, and every real common lower bound g on 1-alpha, on all 1-fract((i+1)*alpha), and on all |fract((i+1)*alpha)-fract((j+1)*alpha)| for distinct i,j in Fin n still gives g/(2*(n+1)) <= radius. No smaller radius or second application at a different horizon is needed. This uses the existential radius and its guarantees, without identifying it with a separately specified minimum or claiming it is maximal. Let 0 <= delta <= radius, beta = alpha+delta, and I = [0,1).

For i in Fin n, write c_i = 1-fract((i.val+1)*alpha) and C_i = [c_i-(i.val+1)*delta,c_i). Thus k = i.val+1 identifies these with the swept intervals above. Set U = union_i C_i, last = n-1 as an element of Fin n, A = C_last, and B = U minus A. Define H(x) = card {j in Fin n | lowerMechanicalWord(beta,x,j.val) != lowerMechanicalWord(alpha,x,j.val)}. In particular H counts unequal Boolean observations at the same phase and times, rather than signed letter changes. The existing slopeDisagreement definition and local_slope_disagreement_law give U = slopeDisagreement(alpha,beta,n), U contained in I, and pairwise disjoint C_i.

To derive the actual mismatch count on C_i, use lowerMechanicalLetter_eq_zero_or_one from D5/S1/Words/Mechanical/MechanicalBalance at both slopes. Its hypotheses hold because 0 < alpha <= beta < 1. Together with the definition of lowerMechanicalWord, equivalently lowerMechanicalWord_eq_true_iff in that same module, this says the Boolean words agree exactly when their integer letters agree. The signed-change conclusion of local_slope_disagreement_law therefore gives a mismatch exactly at j.val = i.val or j.val = i.val+1. For i = last only the first time belongs to Fin n, so H(x) = 1 on A; for i != last both distinct times belong to Fin n, so H(x) = 2 on B. Outside U but inside I, the definition of slopeDisagreement excludes every mismatch, hence H(x) = 0.

Consequently the exact phase fibers are {x in I | H(x)=1} = A, {x in I | H(x)=2} = B, and {x in I | H(x)=0} = I minus U. For every natural q other than 0, 1, and 2, {x in I | H(x)=q} is empty. With m denoting real Lebesgue measure, the last interval has length m(A) = n*delta, while the supplied union measure is m(U) = n*(n+1)*delta/2. Since A is contained in U and U is contained in I, finite-measure subtraction gives m(B) = m(U)-m(A) = n*(n-1)*delta/2 and m(I minus U) = 1-n*(n+1)*delta/2. These are also the probabilities of H=1, H=2, and H=0 for a uniformly distributed phase on I; the inclusions ensure that each mass is nonnegative.

The intervals C_i and their finite union U are measurable, so A and B are measurable subsets of the finite-measure interval I. On I, the real-valued actual count equals the simple function 1_A + 2*1_B, where 1_S denotes the indicator of S. Thus x in I mapped to (H(x) as a real number) is measurable on the subtype I, and the actual real-valued H is almost everywhere strongly measurable and integrable for Lebesgue measure restricted to I. Integrating this pointwise identity yields integral_I H(x) dx = m(A)+2*m(B) = n*delta+n*(n-1)*delta = n^2*delta. This derives both integrability and the integral from the actual count, without assuming either or supplying a separate Hamming pattern.

All sets retain their exact half-open endpoints, including when delta = radius. At delta = 0 every C_i is empty, H vanishes throughout I, and the three masses are 0, 0, and 1. When n = 1, A = U and B is empty, so the H=2 mass vanishes and the integral is delta. The distribution is confined to this local nonnegative perturbation range; beta may be rational. Its interior sweeps change two adjacent bits with opposite signs, while the last sweep changes only the final observed bit because the compensating change lies beyond the horizon. These phase-dependent adjacent exchanges supply no independent-bit error assumption.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.local_slope_disagreement_law`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalSlopeSensitivity.slopeDisagreement`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
