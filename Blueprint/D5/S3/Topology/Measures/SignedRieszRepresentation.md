# Real signed Riesz representation

## Abstract

Regular signed measures form the real continuous dual of a compact Hausdorff Borel space, with exact total variation norm and uniqueness.

K carries TopologicalSpace, CompactSpace, T2Space, MeasurableSpace and BorelSpace structures in an arbitrary universe. The input F is an arbitrary StrongDual Real C(K,Real), with neither positivity nor nonzero norm assumed. signedFunctional is the actual vector-measure signed integral used in NormPreservingLifts. Regularity means regularity of the actual totalVariation measure. SignedMeasure already supplies its finiteness.

**Theorem 1.1 (Regular signed representation, uniqueness and exact norm).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \operatorname{CompactHausdorffBorel}\left(K\right) \Rightarrow\\{\forall s: \operatorname{SignedMeasure}\left(K\right), \forall t: \operatorname{SignedMeasure}\left(K\right), \operatorname{Regular}\left(\operatorname{totalVariation}\left(s\right)\right) \land \operatorname{Regular}\left(\operatorname{totalVariation}\left(t\right)\right) \land \operatorname{signedFunctional}\left(s\right) = \operatorname{signedFunctional}\left(t\right) \Rightarrow s = t} \land\\{\forall s: \operatorname{SignedMeasure}\left(K\right), \operatorname{Regular}\left(\operatorname{totalVariation}\left(s\right)\right) \Rightarrow \operatorname{totalVariationRealUniv}\left(s\right) = \operatorname{norm}\left(\operatorname{signedFunctional}\left(s\right)\right)} \land\\{\forall F: \operatorname{StrongDual}\left(\operatorname{Real}\left(\right), \operatorname{ContinuousMap}\left(K, \operatorname{Real}\left(\right)\right)\right), \exists s: \operatorname{SignedMeasure}\left(K\right), \operatorname{Regular}\left(\operatorname{totalVariation}\left(s\right)\right) \land \operatorname{signedFunctional}\left(s\right) = F \land \operatorname{totalVariationRealUniv}\left(s\right) = \operatorname{norm}\left(F\right)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedRieszRepresentation.signed_riesz_markov_kakutani` (`✓ std3`). ∎

*Citation.* Walter Rudin (1987). *Real and Complex Analysis, third edition*. URL: <https://en.wikipedia.org/wiki/Riesz%E2%80%93Markov%E2%80%93Kakutani_representation_theorem>.

*Commentary.*

For nonempty K define J(f,t) on the disjoint union of two copies of K by t+f on the left and t-f on the right. Its supremum norm is exactly abs(t)+norm(f). The upper inequality is the triangle inequality. For every x, one of the two values, with its sign chosen from the signs of t and f(x), has absolute value abs(t)+abs(f(x)). Taking the supremum gives the reverse inequality. J is injective, but is not an isometry for the usual maximum norm on C(K,Real) times Real.

On the range of J define L(J(f,t))=F(f)+norm(F)*t. The norm identity bounds L by norm(F). Hahn–Banach gives a norm-preserving extension G to C(K disjoint-union K,Real). The unit is J(0,1), so G(1)=norm(F) and norm(G) is at most G(1). The order-unit positivity theorem makes G positive. Its restrictions to the two summands give positive functionals P,Q with P-Q=F and P(1)+Q(1)=norm(F).

Positive Riesz–Markov–Kakutani on K gives finite regular measures mu and nu representing P and Q. Their real masses sum to norm(F). For s=mu.toSignedMeasure-nu.toSignedMeasure, the signed difference integral formula proves signedFunctional(s)=F. The scalar pairing is identified explicitly with its flipped pairing by commutativity of real multiplication.

The variation inequality gives totalVariation(s) at most mu+nu. Finite domination transports compact inner approximation: for r less than rho(A), choose a compact closed C inside A with sigma(A minus C) less than rho(A)-r. Domination and the measurable partition of A force rho(C)>r. The finite Borel R1 regularity theorem then supplies regularity of rho. This applies to the signed variation dominated by the finite regular sum. Its mass is at most norm(F); the signed integration operator bound gives the reverse inequality.

If K is empty, C(K,Real) and its dual are zero and the representative is zero. The nonempty construction divides by no quantity, so norm(F)=0 is included. No metric, separability or countable family of tests is required.

For uniqueness let a,b be the positive and negative Jordan parts of s and d,e those of t. RegularSignedLift.regular_jordanParts_of_regular_totalVariation makes all four parts regular. Equal signed functionals give equal continuous integrals for the positive finite regular measures a+e and b+d. Measure.ext_of_integral_eq_on_compactlySupported identifies these sums. Applying Measure.toSignedMeasure_congr and Measure.toSignedMeasure_add, then the signed Jordan reconstruction, yields s=t. No regularity of s-t is assumed.

For any regular signed s, apply the arbitrary-dual construction to signedFunctional(s). Its regular representative t has variation mass equal to the operator norm. Independently proved uniqueness gives t=s, so every regular signed measure has exact total variation norm. This argument uses only the one-sided integration bound in the construction, and does not use the universal norm identity to prove either existence or uniqueness.

## References

- Truth anchor: `D5/S3/Topology/Measures/SignedRieszRepresentation.signed_riesz_markov_kakutani`
- Dependency: [D5/S3/Topology/Measures/NormPreservingLifts](NormPreservingLifts.md)
- Dependency: [D5/S3/Topology/Measures/RegularSignedLift](RegularSignedLift.md)
