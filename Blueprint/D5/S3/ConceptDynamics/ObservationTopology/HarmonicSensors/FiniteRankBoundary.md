# Finite Paired Harmonic Rank Boundary

## Abstract

Two positive harmonic pairs have rank at most four thirds; three pairs can approach two, and every finite injective paired family has rank strictly below two.

Let I be a finite nonempty index set, k an injective map from I to positive natural frequencies, and a a positive real amplitude at every index. The physical state is x(phi)=(cos(phi),sin(phi)). The sensor H(phi) has coordinate pair a(i)(cos(k(i)phi),sin(k(i)phi)) for each i. Physical injectivity means that equality of sensor outputs implies equality of x(phi) and x(psi). PhysicalFamily(I,k,a) denotes exactly these assumptions, including physical injectivity.

Set theta=pi/6. The delay matrix X(phi) has rows H(phi) and H(phi-theta). R(k,a) is the infimum, over all x(phi) unequal to x(psi), of the squared Frobenius norm of X(phi)-X(psi) divided by its squared Euclidean operator norm. No phase interval is removed from this infimum. For d=phi-psi, write A(d)=4 sum_i a(i)^2 sin(k(i)d/2)^2 and B(d)=4 sum_i a(i)^2 cos(k(i)theta) sin(k(i)d/2)^2. The row Gram matrix has diagonal A and off-diagonal B. Its actual norm formulas give the chord rank 2/(1+abs(B)/A), and injectivity gives A>0.

**Theorem 1.1 (The complete one-or-two-pair upper bound).**

$$\forall I \in FiniteNonemptyTypes, k \in \operatorname{NaturalFrequencyMaps}\left(I\right), a \in \operatorname{RealAmplitudeMaps}\left(I\right),\; \operatorname{PhysicalFamily}\left(I, k, a\right) \Rightarrow \left(\operatorname{card}\left(I\right) \le 2 \Rightarrow \operatorname{R}\left(k, a\right) \le \frac{4}{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.at_most_two_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a single frequency, the physical kernel theorem forces frequency one. Every nonzero chord then has B/A=cos(pi/6), whose absolute value exceeds one half.

For distinct frequencies m and n, injectivity gives gcd(m,n)=1. When n>1, the chord d=2pi/n is a pair of distinct physical states. The n-th difference vanishes. The remaining energy is positive by injectivity, so B/A=cos(m pi/6) on this chord. If both frequencies exceed one, both endpoints are available and the coprime cosine obstruction supplies one with magnitude at least one half. If one frequency is one, isolate that frequency by killing the other. The physical infimum is therefore at most four thirds in all cases.

**Theorem 1.2 (Sharp attainment and unit derivative).**

$$\forall a \in PositiveAmplitudes2,\; \operatorname{PhysicallyInjective}\left(k23, a\right) \land \left(\operatorname{R}\left(k23, a\right) = \frac{4}{3} \land \left(\exists b \in \operatorname{RealAmplitudeMaps}\left(Fin2\right),\; \left(\forall i \in Fin2,\; \operatorname{component}\left(b, i\right) = \frac{\operatorname{component}\left(a, i\right)}{\operatorname{sqrt}\left(4 \cdot \operatorname{component}\left(a, 0\right)^{2} + 9 \cdot \operatorname{component}\left(a, 1\right)^{2}\right)}\right) \land \left(\operatorname{PositiveAmplitudes2}\left(b\right) \land \left(\operatorname{PhysicallyInjective}\left(k23, b\right) \land \left(\operatorname{R}\left(k23, b\right) = \frac{4}{3} \land \left(\forall phi \in Real,\; \operatorname{derivativeNorm}\left(k23, b, phi\right) = 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.two_three_attainment_and_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In this formula k23=(2,3), PositiveAmplitudes2 consists of arbitrary positive real pairs, RealAmplitudeMaps(Fin2) consists of all real amplitude maps on Fin2={0,1}, and component(a,i)=a(i). The existential witness b satisfies, for every i in Fin2, b(i)=a(i)/sqrt(4a(0)^2+9a(1)^2), exactly as in the Lean conclusion. Both the original and normalized sensors are physically injective. At frequencies two and three the two cosine coefficients are one half and zero. Nonnegativity of the two harmonic energies gives abs(B)<=A/2 on every physical chord. Together with the upper bound this gives R=4/3 for every positive amplitude pair.

The derivative of each planar pair has squared norm k(i)^2 a(i)^2. The pairs occupy orthogonal coordinates, so the squared norm of the full derivative is 4a(0)^2+9a(1)^2. Dividing the amplitudes by the positive square root of this quantity gives derivative norm one at every phase. The arbitrary-amplitude result gives rank four thirds for this normalized sensor as well.

**Theorem 1.3 (Strict nonattainment for every finite positive family).**

$$\forall I \in FiniteNonemptyTypes, k \in \operatorname{NaturalFrequencyMaps}\left(I\right), a \in \operatorname{RealAmplitudeMaps}\left(I\right),\; \operatorname{PhysicalFamily}\left(I, k, a\right) \Rightarrow \operatorname{R}\left(k, a\right) < 2$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.finite_rank_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose R>=2. Each physical chord has positive energy, and the actual norm formula then forces B(d)=0 on every distinct-state chord. When x(d)=x(0), d is an integer multiple of 2pi, so all harmonic sine differences vanish and B(d)=0 there also.

Write w(i)=a(i)^2 and c(i)=cos(k(i)theta). The half-angle identity now gives sum_i w(i)c(i)=sum_i w(i)c(i)cos(k(i)d) for every d. Integrating over a full period makes the right side zero, since each frequency is a positive integer. Evaluating the same identity at d=theta gives sum_i w(i)c(i)^2=0. Each w(i)>0, so every c(i)=0.

At d=2pi/3=4theta, the half-chord sine is sin(2k(i)theta)=2sin(k(i)theta)cos(k(i)theta)=0. Thus A(d)=0. This is a distinct physical third-turn chord, contradicting injectivity. Hence R<2.

**Theorem 1.4 (Exactly three pairs are necessary and sufficient to approach two).**

$$\operatorname{IsLeast}\left(ApproachingPairCounts, 3\right) \land \operatorname{realDimension}\left(\operatorname{EuclideanPairedSpace}\left(3\right)\right) = 6$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.minimum_pair_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

EuclideanPairedSpace(n) is the real Euclidean space indexed by Fin n times Fin 2. ApproachingPairCounts is the set of natural numbers n such that for every real r<2 there exist positive amplitudes and distinct positive frequencies indexed by Fin n, with physically injective sensor and R>r. The empty family is not injective. The one- and two-pair bound excludes both smaller positive counts, for example by taking r=3/2.

For sufficiency use the actual six-coordinate family with frequencies (2,3,4), amplitudes (sqrt(epsilon),1,sqrt(epsilon))/sqrt(9+20epsilon), and 0<epsilon<=1/2. Its gcd is one and all amplitudes are positive. The physical rank-defect limit (2-R)/sqrt(epsilon/2) -> 1 implies R -> 2 from positive epsilon. Consequently these three-pair sensors satisfy every threshold r<2. The strict finite-family result shows that no such sensor, nor any other finite sensor in this class, reaches two exactly.

The sensor-design question in `D5/L/ConceptDynamics/eftekhari2018embedology` motivates the stable-rank comparison. The pair count here concerns the specified positive harmonic pairs at two fixed delays. It is not a minimum-dimension theorem for arbitrary smooth sensors or arbitrary delay schemes.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.at_most_two_pairs`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.finite_rank_strict`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.minimum_pair_count`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/FiniteRankBoundary.two_three_attainment_and_normalization`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/HarmonicSensors/SixDimensionalSharpGeometry](SixDimensionalSharpGeometry.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/TwoHarmonicRotationObstruction](../TwoHarmonicRotationObstruction.md)
