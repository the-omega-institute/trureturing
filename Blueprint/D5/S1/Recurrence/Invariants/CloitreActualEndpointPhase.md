# Actual Cloitre Endpoint Phase and Defect Amplitude

## Abstract

Under the full actual Cloitre hypotheses, every sufficiently high positive right width selects the endpoint two-cycle with absolute time phase and canonical defect amplitude.

F is the Fibonacci sequence with F(0)=0 and F(1)=1. G(n) is the natural floor of (n+1) divided by the golden ratio. C, T, X, d, g, I and Hyp21_1 are the actual finite-prefix Cloitre definitions of CloitreActualRightProfile. In particular, X(N,0)=N-1, T(N,x)=N-C(x), d(N)=C(N-1), and g(N)=X(N,d(N)). All conclusions retain the complete Hyp21_1 premise bundle, including its finite source foundations and global orbit relations.

**Definition 1.1 (Canonical golden defect).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.canonicalDefect`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.canonicalDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

canonicalDefect(n)=C(n)-G(n) uses natural subtraction. Hyp21_1 ensures G(n)<=C(n) for every positive n, so this equals the nonnegative integer golden defect there. It is distinct from a right-profile deficit.

**Definition 1.2 (Right-width defect).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.widthDefect`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.widthDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

widthDefect(t)=t-G(t). This is the canonical defect at the selected upper endpoint at the admissible Fibonacci orders.

**Definition 1.3 (The complete orbit of the actual selector).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.selectedOrbit`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.selectedOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

selectedOrbit(N) is the range of all nonnegative iterates of T(N) starting at g(N), the prescribed-depth point of the actual orbit from N-1.

**Definition 1.4 (Canonical oscillation on the selected pair).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.selectedPairAmplitude`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.selectedPairAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

selectedPairAmplitude(N) is the maximum minus the minimum of canonicalDefect at g(N) and T(N,g(N)). The theorem proves that these two entries exhaust the selectedOrbit in both the positive-width and zero-width cases. Consequently this pair oscillation is the canonical defect amplitude of the whole selected cycle in those cases.

**Definition 1.5 (Every positive-width endpoint clause).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.EndpointPhase`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.EndpointPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With N=F(k)+t and A=F(k-1), there exists a first collar-entry time mu: X(N,mu) lies in I(k,t), and all earlier X(N,i) lie outside it. Mu is even and X(N,mu)=A+t. This point is periodic, all earlier points are not periodic, and mu<=d(N); thus mu is the shortest preperiod. For every i>=mu, X(N,i)=A+t at even absolute times i and A at odd absolute times. Exactly d(N)=A+t-1, and g(N)=A+t if A+t-1 is even and A otherwise. The minimal selected period is exactly two, and selectedOrbit(N) is exactly {A,A+t}. The endpoint canonical defects are zero and widthDefect(t), respectively, and selectedPairAmplitude(N)=widthDefect(t).

**Definition 1.6 (The separate zero-offset fixed-point branch).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.ZeroPhase`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.ZeroPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With N=F(k) and A=F(k-1), the actual orbit first reaches A at some mu, all earlier points differ from A and are not periodic, X(N,mu) is periodic, and mu<=d(N). Every i>=mu has X(N,i)=A. The actual selector is g(N)=A, its minimal period is one, and selectedOrbit(N)={A}. Its canonical defect and selectedPairAmplitude are both zero. This branch uses no positive-width parity formula.

**Theorem 1.7 (Complete conditional endpoint theorem).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.full22_1`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.full22_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural-valued function U satisfying the original Hyp21_1, every natural t>=1 and k>=12*t+7 satisfy EndpointPhase(t,k). WidthDefect(1)=0 even though its selected endpoints are distinct and the period is two. Every t>=2 has widthDefect(t)>0. For every M,t,k with t>=3*M+2 and k>=12*t+7, selectedPairAmplitude(F(k)+t)>M and the minimal selected period remains exactly two. This uniform bound permits an arbitrary admissible order k at each width t and gives divergence as t tends to infinity. Every k>=6 satisfies ZeroPhase(k).

The right-profile theorem full21_3 supplies collar reflection and the exact depth. The upper cap gives left exterior images at least A+t. The profile on widths through 2*t, together with the exact golden floor and its Fibonacci successor anchor, puts every right exterior image strictly below A. Exterior alternation from the actual origin N-1 therefore forces an even first entry at A+t; reflection preserves its absolute phase. The public Zeckendorf displacement readout and greatest-Fibonacci digit equation give G(A+t)=F(k-2)+G(t), so the complete endpoint cycle has the stated canonical defect oscillation. The golden inverse lies below two thirds, which gives the uniform growth bound. This conditional theorem supplies no inhabitant of Hyp21_1 and no independent certificate of its finite or global source premises.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.EndpointPhase`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.ZeroPhase`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.canonicalDefect`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.full22_1`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.selectedOrbit`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.selectedPairAmplitude`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase.widthDefect`
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](../../Deficit/ZeckendorfDisplacementReading.md)
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualRightProfile](CloitreActualRightProfile.md)
