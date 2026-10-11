# Intrinsic Circle Graph Charts

## Abstract

An analytic intrinsic Circle map into a finite dimensional real inner product space has actual immersion charts when its intrinsic differential is injective.

**Theorem 1.1 (One fixed complement and actual normal form charts).**

$$\begin{gathered}\forall V, f: Circle \to V,\\{}\operatorname{FiniteDimensionalRealInnerProductSpace}\left(V\right) \land \operatorname{ContMDiff}\left(R1, \operatorname{I}\left(Real, V\right), top, f\right) \land (\forall z, \operatorname{Injective}\left(\operatorname{mvfderiv}\left(R1, f, z\right)\right)) \Rightarrow\\{}\operatorname{IsImmersionOfComplement}\left(\operatorname{EuclideanSpace}\left(Real, \operatorname{Fin}\left(\operatorname{finrank}\left(Real, V\right) - 1\right)\right), R1, \operatorname{I}\left(Real, V\right), top, f\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.isImmersionOfComplement_of_contMDiff_injective_mvfderiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient space V is a finite dimensional real inner product space. The map f is analytic: top in NatInfinityOmega is omega, whereas infinity denotes smooth regularity. R1 denotes the actual Circle model 𝓡 1, and I(Real,V) denotes the real self model 𝓘(ℝ, V). Its intrinsic differential is injective at every Circle point.

Fix E to be EuclideanSpace ℝ (Fin 1) and W to be EuclideanSpace ℝ (Fin (Module.finrank ℝ V - 1)), with subtraction in the natural numbers. In the formula, Real denotes ℝ and finrank denotes Module.finrank over the indicated field. At a Circle point z, let c = chartAt E z be the existing stereographic Circle chart, q = c(z), g = f ∘ c.symm, and D = fderiv ℝ g q. The orthogonal complement of D.range has the dimension of W. A continuous linear equivalence identifies it with W and extends D to a continuous linear equivalence L : (E × W) ≃L[ℝ] V satisfying L(u,0) = D(u) for every u in E.

Define H at L(u,w) to be g(u) plus L(0,w). The derivative of H at L(q,0) is the identity. The inverse function theorem supplies an actual open partial homeomorphism for H and proves the regularity of its inverse.

Restrict this inverse to an open set where both directions have the required regularity, and call the resulting ambient chart cod. Its forward and inverse regularity give membership in the ambient maximal atlas. Restrict c to the points whose L(u,0) lies in cod.target, and call the resulting domain chart dom.

These charts satisfy dom.source ⊆ f⁻¹(cod.source). For every u in dom.target, cod(f(dom.symm(u))) = L(u,0). The source inclusion follows from the ambient inverse mapping property. The exact chart equation follows from H(L(u,0)) = g(u) and cod.right_inv.

The construction uses the existing stereographic atlas, finite dimensional orthogonal decomposition, and inverse function theorem. This is the classical local graph construction for this intrinsic Circle model.

**Definition 1.2 (Actual intrinsic Circle sensor with real paired output).**

$$\begin{gathered}\forall iota: Type, [\operatorname{Fintype}\left(iota\right)] k: iota \to Nat, a: iota \to Real, \forall z: Circle, \forall i: iota,\\{}\operatorname{coordZero}\left(\operatorname{intrinsicSensor}\left(k, a, z\right), i\right) = \operatorname{a}\left(i\right) \cdot \operatorname{realPart}\left(\operatorname{pow}\left(\operatorname{ofComplex}\left(z\right), \operatorname{k}\left(i\right)\right)\right) \land \operatorname{coordOne}\left(\operatorname{intrinsicSensor}\left(k, a, z\right), i\right) = \operatorname{a}\left(i\right) \cdot \operatorname{imagPart}\left(\operatorname{pow}\left(\operatorname{ofComplex}\left(z\right), \operatorname{k}\left(i\right)\right)\right)\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.intrinsicSensor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index type iota, k is a natural frequency family and a is a real amplitude family. Each Circle point z is the actual unit complex number, with the stereographic Circle manifold structure. The coordinate indexed by (i,0) is a(i) times the real part of z raised to k(i); coordinate (i,1) is a(i) times its imaginary part. The output V(iota) is EuclideanSpace Real (iota times Fin 2). The displayed coordZero and coordOne specify all real coordinates of that output; ofComplex denotes the ordinary Circle inclusion into the complex plane.

**Theorem 1.3 (Analytic immersion and exact gcd criterion for embedding).**

$$\begin{gathered}\forall iota: Type, [\operatorname{Fintype}\left(iota\right)][\operatorname{Nonempty}\left(iota\right)] k: iota \to Nat, a: iota \to Real, \\{}(\forall i: iota, 0 < \operatorname{k}\left(i\right)) \land (\forall i: iota, 0 < \operatorname{a}\left(i\right)) \Rightarrow\\{}(\forall phi: Real, \operatorname{intrinsicSensor}\left(k, a, \operatorname{CircleExp}\left(phi\right)\right) = \operatorname{pairedSensor}\left(k, a, phi\right)) \land\\{}\operatorname{ContMDiff}\left(R1, \operatorname{I}\left(Real, \operatorname{EuclideanSpace}\left(Real, iota \times \operatorname{Fin}\left(2\right)\right)\right), top, \operatorname{intrinsicSensor}\left(k, a\right)\right) \land\\{}(\forall z: Circle, \operatorname{Injective}\left(\operatorname{mvfderiv}\left(R1, \operatorname{intrinsicSensor}\left(k, a\right), z\right)\right)) \land\\{}\operatorname{IsImmersionOfComplement}\left(\operatorname{EuclideanSpace}\left(Real, \operatorname{Fin}\left(\operatorname{finrank}\left(Real, \operatorname{EuclideanSpace}\left(Real, iota \times \operatorname{Fin}\left(2\right)\right)\right) - 1\right)\right), R1, \operatorname{I}\left(Real, \operatorname{EuclideanSpace}\left(Real, iota \times \operatorname{Fin}\left(2\right)\right)\right), top, \operatorname{intrinsicSensor}\left(k, a\right)\right) \land\\{}(\operatorname{IsEmbedding}\left(\operatorname{intrinsicSensor}\left(k, a\right)\right) \iff \operatorname{gcd}\left(\operatorname{univ}\left(iota\right), k\right) = 1) \land\\{}((\exists e: \operatorname{Homeomorph}\left(Circle, \operatorname{range}\left(\operatorname{intrinsicSensor}\left(k, a\right)\right)\right), \forall z: Circle, \operatorname{val}\left(\operatorname{e}\left(z\right)\right) = \operatorname{intrinsicSensor}\left(k, a, z\right)) \iff \operatorname{gcd}\left(\operatorname{univ}\left(iota\right), k\right) = 1)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.finite_paired_intrinsic_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type is finite and nonempty. Every k(i) is strictly positive and every a(i) is strictly positive. Distinct frequencies are allowed without further hypotheses; repeated frequencies are covered as well. The original finite nonempty subset of positive natural numbers is obtained by taking its subtype as the index and its inclusion as k. Finset.univ.gcd is the full gcd, not a pairwise coprimality requirement. W(iota) is EuclideanSpace Real (Fin (finrank Real V(iota) minus 1)), the same complement at every point.

H in the formula abbreviates intrinsicSensor(k,a), and the displayed formula expands that abbreviation at each occurrence. The phase bridge is pointwise equality H(Circle.exp(phi)) = pairedSensor(k,a,phi). The auxiliary stateOfCircle map sends z to its two real coordinates, is injective, and at Circle.exp(phi) is exactly circleState(phi). Surjectivity of Circle.exp therefore transports the phase finite_paired_injective_iff_gcd_one criterion to intrinsic Circle injectivity.

Equality of paired readings is equality of all harmonic powers; the finite gcd criterion follows by folding the power-gcd law. For gcd greater than one, the phase d=2 pi/gcd is distinct from zero on the physical circle and aliases at every common delay. Indeed, each frequency is divisible by the gcd, so shifting both phases by any real delay preserves equality of every harmonic power. The ordinary circle chord identity proves that the two physical states are distinct.

The ambient polynomial is smooth and analytic. Recover coordinate pair i as the complex number Q(v) = v(i,0) + I v(i,1). Then Q composed with the ambient sensor is exactly a(i) z raised to k(i). Its real differential sends u to u times a(i) k(i) z raised to k(i)-1. This multiplier is nonzero because a(i)>0, k(i)>0, and a unit complex number is nonzero. The chain rule proves injectivity of the ambient sensor differential. The sphere inclusion has injective differential, so the intrinsic sensor does too. The actual CircleGraph theorem constructs immersion charts with the fixed W(iota).

Compactness of Circle and the Hausdorff Euclidean codomain turn injectivity into a closed embedding. IsEmbedding.toHomeomorph gives the actual map to its range, with pointwise agreement explicitly in the theorem. Conversely, any agreeing homeomorphism forces injectivity, hence gcd one. Immersion holds for every positive nonempty family; it does not require gcd one. For a singleton frequency n>0, the map is immersed for every n and embedded exactly for n=1. Top is analytic regularity, which in particular supplies smoothness.

For the original six-coordinate construction, set k=(2,3,4), Z=9+20 epsilon and a=(sqrt(epsilon),1,sqrt(epsilon))/sqrt(Z). For every epsilon>0 all amplitudes are positive and the gcd is one. The phase bridge identifies this intrinsic sensor after Circle.exp with the six real coordinates in frequency order 2, 3, 4 and these amplitudes. Its embedding pulls the Euclidean topology back to the existing intrinsic Circle topology. Thus every two positive epsilon values induce the same topology. Evaluation at phi minus pi/6 retains the original fixed delay. The finite-epsilon sharp lower-chord and correlation formulas have the separate quantitative range 0<epsilon<=1/2.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.finite_paired_intrinsic_circle`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.intrinsicSensor`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts.isImmersionOfComplement_of_contMDiff_injective_mvfderiv`
