# Round-Trip Classification from Ray Continuity

## Abstract

Round-Trip Classification from Ray Continuity.

**Theorem 1.1 (Round-Trip Classification from Ray Continuity).**

$$\forall A \in Type,\; [\operatorname{NormedRing}\left(A\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall L \in \operatorname{LieSubalgebra}\left(\mathbb{R}, A\right),\; \forall G \in \operatorname{Subgroup}\left(\operatorname{Units}\left(A\right)\right),\; \forall D \in \operatorname{ContinuousData}\left(L, G\right),\; \exists h \in \operatorname{BilinForm}\left(\mathbb{R}, L\right),\; \operatorname{IsSymm}\left(h\right) \land \left(\left(\forall X \in L,\; h\left(X, X\right) \ge 0\right) \land \left(\left(\forall X \in L,\; h\left(X, X\right) = 0 \Rightarrow X = 0\right) \land \left(\left(\forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{phi}\left(D\right)\left(\operatorname{exp}\left(D\right)\left((t \cdot X)\right)\right) = \operatorname{cos}\left((t \cdot \operatorname{sqrt}\left(\frac{h\left(X, X\right)}{2}\right))\right)^{2}\right) \land \left(\left(\forall X \in L,\; X \ne 0 \Rightarrow \left(\exists T \in \mathbb{R},\; T > 0 \land \left(\left(\forall t \in \mathbb{R},\; \operatorname{exp}\left(D\right)\left((t \cdot X)\right) = 1 \Leftrightarrow \left(\exists k \in \mathbb{Z},\; t = (T \cdot k)\right)\right) \land h\left(X, X\right) = \frac{(2 \cdot \pi^{2})}{T^{2}}\right)\right)\right) \land \left(\left(\forall t \in \mathbb{R},\; \forall X \in L,\; \operatorname{exp}\left(D\right)\left((t \cdot X)\right) = 1 \Leftrightarrow \left(\exists n \in \mathbb{Z},\; (t \cdot \operatorname{sqrt}\left(\frac{h\left(X, X\right)}{2}\right)) = (\pi \cdot n)\right)\right) \land \left(\left(\forall X \in L,\; \forall Y \in L,\; \operatorname{bracket}\left(X, Y\right) = 0 \Rightarrow \left(X = 0 \lor \left(\exists c \in \mathbb{R},\; Y = (c \cdot X)\right)\right)\right) \land \left(\left(\forall C \in L,\; \forall X \in L,\; \forall Y \in L,\; h\left(\operatorname{bracket}\left(C, X\right), Y\right)+h\left(X, \operatorname{bracket}\left(C, Y\right)\right) = 0\right) \land \left(\left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 0 \lor \left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 1 \lor \operatorname{finrank}\left(\mathbb{R}, L\right) = 3\right)\right) \land \left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 3 \Rightarrow \left(\exists b \in \operatorname{Basis}\left(\operatorname{Fin}\left(3\right), \mathbb{R}, L\right),\; \exists mu \in \mathbb{R},\; mu > 0 \land \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; h\left(b\left(i\right), b\left(j\right)\right) = \operatorname{if} (i = j) \operatorname{then} 1 \operatorname{else} 0\right) \land \left(\operatorname{bracket}\left(b\left(0\right), b\left(1\right)\right) = (mu \cdot b\left(2\right)) \land \left(\operatorname{bracket}\left(b\left(1\right), b\left(2\right)\right) = (mu \cdot b\left(0\right)) \land \operatorname{bracket}\left(b\left(2\right), b\left(0\right)\right) = (mu \cdot b\left(1\right))\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/RoundTripPeriodMetric.comparison_classification_of_continuous_rays` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complete finite-dimensional real normed associative unital algebra. Let L be a real Lie subalgebra of A for the commutator, and let G be a subgroup of its units. The data ContinuousData(L,G) comprise the function phi on G, membership of exp(X) in G for each X in L, and preservation of L under conjugation by G. The function takes values in [0,1], equals 1 precisely at the identity, satisfies the duplication law phi(g*g)=(2*phi(g)-1)^2, and is invariant under conjugation. For each X, the real function t ↦ phi(exp(tX)) is continuous.

Every nonzero direction has a positive return time. Its return times are the integer multiples of the least positive return time T. The comparison is the square of the cosine at angular frequency pi/T on this ray, and the symmetric bilinear form h satisfies h(X,X)=2*pi^2/T^2.

In the complexified left regular representation, a generator with periodic exponential has an eigenbasis with integral frequencies after rescaling by a return time. The negative trace of its square is positive in each nonzero direction. After dividing the generator by the square root of this trace form, the characteristic determinant has countable range. It is constant on the connected punctured space in dimension at least two. The one-dimensional case follows from scaling a generator. The common return lattice of normalized directions then determines the scalar multiple of the trace form that gives h.

The resulting cosine formula and the bound of the bilinear form by the inherited algebra norm squared give the quadratic expansion at zero. Consequently h is positive definite and infinitesimally invariant. Commuting pairs are dependent, the dimension is zero, one or three, and the dimension-three space has an h-orthonormal basis with one positive cyclic bracket constant.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/RoundTripPeriodMetric.comparison_classification_of_continuous_rays`
- Dependency: [D5/S3/Analytic/Dilation/DuplicationCircleRigidity](../../../Analytic/Dilation/DuplicationCircleRigidity.md)
- Dependency: [D5/S3/Quantum/Algebra/Comparison/RoundTripClassification](RoundTripClassification.md)
