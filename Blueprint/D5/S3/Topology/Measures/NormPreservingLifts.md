# Arbitrary signed lifts and weak-star stability

## Abstract

Norm-preserving signed lifts on compact spaces inherit a reference weak-star limit when each fixed locally constant test is eventually constant on supported projection fibres.

K is compact Hausdorff and totally disconnected, with its Borel measurable structure. L is Hausdorff with its Borel structure. The carrier universes u and v and index universe w are independent. The index filter l is arbitrary: neither a sequence nor a nontrivial-filter assumption is needed. A continuous p from K to L is used as an actual measurable pushforward. The proof works without surjectivity or compactness of L, so continuous compact quotient maps are included.

signedFunctional(s) is the continuous linear map from C(K,Real) to Real given by the actual vector-measure signed integral of f against s, with scalar multiplication as its bilinear pairing. Its operator norm is bounded by the real total mass of the Hahn–Jordan totalVariation of s. SignedMeasure itself is not assigned a normed-space instance. weakSignedFunctional(s) means pointwise application of StrongDual.toWeakDual to this functional. totalVariationMass(s) means totalVariation(s)(univ), an extended nonnegative real; toReal is used only for its finite total mass.

**Theorem 1.1 (Signed integration of a positive difference).**

$$\forall K: \operatorname{Type}\left(u\right), \operatorname{CompactBorel}\left(K\right) \Rightarrow\forall mu: \operatorname{FiniteMeasure}\left(K\right), \forall nu: \operatorname{FiniteMeasure}\left(K\right), \forall f: \operatorname{ContinuousMap}\left(K, \operatorname{Real}\left(\right)\right), \operatorname{signedFunctional}\left(\operatorname{signedDifference}\left(mu, nu\right), f\right) = \operatorname{integral}\left(f, mu\right) - \operatorname{integral}\left(f, nu\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.signedFunctional_sub_toSignedMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite positive measures mu and nu on compact Borel K, the signed functional of their signed difference evaluates f as the difference of ordinary integrals. Continuity gives the required integrability against finite variations. Real multiplication identifies the scalar pairing with its flip, so Mathlib's integral_toSignedMeasure applies. No separation or regularity hypothesis is used.

**Theorem 1.2 (Variation domination for positive differences).**

$$\forall K: \operatorname{Type}\left(u\right), \operatorname{MeasurableSpace}\left(K\right) \Rightarrow\forall mu: \operatorname{FiniteMeasure}\left(K\right), \forall nu: \operatorname{FiniteMeasure}\left(K\right), \operatorname{totalVariation}\left(\operatorname{signedDifference}\left(mu, nu\right)\right) \le mu + nu$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.totalVariation_sub_toSignedMeasure_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable carrier, the total variation of mu.toSignedMeasure minus nu.toSignedMeasure is dominated by mu+nu. This is the variation subtraction inequality together with variation_toSignedMeasure. It does not require the two positive measures to be mutually singular or to be Jordan parts.

**Theorem 1.3 (Signed integration operator bound).**

$$\forall K: \operatorname{Type}\left(u\right), \operatorname{CompactBorel}\left(K\right) \Rightarrow \forall s: \operatorname{SignedMeasure}\left(K\right), \operatorname{norm}\left(\operatorname{signedFunctional}\left(s\right)\right) \le \operatorname{totalVariationRealUniv}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.signedFunctional_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original continuous-linear-map construction bounds the operator norm of actual signed integration by totalVariation.real(univ). ClopenCauchyConvergence directly consumes this supplier.

**Theorem 1.4 (Preserved mass makes variation commute with pushforward).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), \forall Y: \operatorname{Type}\left(v\right), \operatorname{MeasurableSpaces}\left(X, Y\right) \Rightarrow\\\forall s: \operatorname{SignedMeasure}\left(X\right), \forall p: X \to Y, \operatorname{Measurable}\left(p\right) \Rightarrow\\\operatorname{totalVariation}\left(\operatorname{map}\left(s, p\right), \operatorname{univ}\left(\right)\right) = \operatorname{totalVariation}\left(s, \operatorname{univ}\left(\right)\right) \Rightarrow\\\operatorname{totalVariation}\left(\operatorname{map}\left(s, p\right)\right) = \operatorname{map}\left(\operatorname{totalVariation}\left(s\right), p\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.totalVariation_map_of_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X and Y carry measurable spaces, s is an actual signed measure on X, and p is measurable. If pushing s forward preserves its entire total variation mass, then the positive measures totalVariation(map(s,p)) and map(totalVariation(s),p) are equal. The proof combines Mathlib's variation_map_le with equality of finite measures from domination and equal total mass. No topology, surjectivity, mass-one normalization or regularity premise is required.

**Theorem 1.5 (Supported lifts agree on a fibre-constant clopen).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \forall L: \operatorname{Type}\left(v\right), \operatorname{CompactBorel}\left(K\right) \land \operatorname{HausdorffBorel}\left(L\right) \Rightarrow\\\forall p: K \to L, \operatorname{Continuous}\left(p\right) \Rightarrow\\\forall V: \operatorname{Set}\left(L\right), \forall A: \operatorname{Set}\left(K\right), \operatorname{IsClopen}\left(V\right) \land \operatorname{IsClopen}\left(A\right) \Rightarrow\\\forall s: \operatorname{SignedMeasure}\left(K\right), \forall t: \operatorname{SignedMeasure}\left(K\right), \operatorname{map}\left(s, p\right) = \operatorname{map}\left(t, p\right) \Rightarrow\\\operatorname{totalVariation}\left(s, \operatorname{compl}\left(\operatorname{preimage}\left(p, V\right)\right)\right) = 0 \land \operatorname{totalVariation}\left(t, \operatorname{compl}\left(\operatorname{preimage}\left(p, V\right)\right)\right) = 0 \Rightarrow\\\operatorname{FibreConstantOn}\left(\operatorname{indicator}\left(A\right), p, V\right) \Rightarrow\operatorname{s}\left(A\right) = \operatorname{t}\left(A\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.apply_eq_of_supported_clopen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is compact with its Borel structure; L is Hausdorff with its Borel structure. The map p is continuous. V in L and A in K are clopen. The signed measures s and t have the same pushforward and give zero total variation to the complement of p-preimage(V). FibreConstantOn(indicator(A),p,V) means that p(x),p(y) in V and p(x)=p(y) imply x in A if and only if y in A. Then s(A)=t(A). Neither Hausdorffness of K nor surjectivity of p is needed.

The compact image p[A intersect p-preimage(V)] is closed in L. Its preimage differs from A only off the common support. Zero variation on both set differences identifies each signed evaluation with its pushforward evaluation on that image.

For a fixed finite coordinate test, each clopen atom is an A of this kind once the supported fibres are constant on those coordinates. Norm-preserving lifts first obtain their common positive pushforward and support from totalVariation_map_of_mass. Applying this clopen comparison gives equality of their signed atom values. For positive-variation atom values, convert the finite measures totalVariation(s) and totalVariation(t) with Measure.toSignedMeasure. Their signed pushforwards agree by the common positive pushforward; Measure.variation_toSignedMeasure preserves the same concentration hypotheses. The same clopen comparison then gives equality of real positive evaluations, hence equality of the finite measure values. This argument does not claim that variation commutes with the finite coordinate map.

A finite sum of the reference atom errors consequently bounds every lift at once, provided that the finitely many reference evaluations converge. Signed weak-star convergence gives signed clopen evaluation convergence by the continuous clopen indicator. For positive evaluations, extract a separate probability-measure limit of the mass-one variations on a compact metric carrier and use clopen convergence for that probability limit. The probability limit is not identified with the variation of a signed weak-star limit. A finite coordinate family is fixed before choosing its tail; moving families require a new finite-stage choice. These are applications of the existing comparison, not a construction of the successor space, its split traces, the transfinite recursion or the final analytic endpoints.

**Theorem 1.6 (Every norm-preserving choice has the reference limit).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \forall L: \operatorname{Type}\left(v\right), \forall I: \operatorname{Type}\left(w\right), \\\operatorname{CompactHausdorffTotallyDisconnected}\left(K\right) \land \operatorname{Hausdorff}\left(L\right) \land \operatorname{BorelSpaces}\left(K, L\right) \Rightarrow\\\forall l: \operatorname{Filter}\left(I\right), \forall p: K \to L, \operatorname{Continuous}\left(p\right) \Rightarrow\\\forall V: I \to \operatorname{Set}\left(L\right), \forall nu: I \to \operatorname{SignedMeasure}\left(L\right), \\\forall s: I \to \operatorname{SignedMeasure}\left(K\right), \forall t: I \to \operatorname{SignedMeasure}\left(K\right), \forall C: \operatorname{Real}\left(\right), \forall F: \operatorname{WeakDual}\left(\operatorname{Real}\left(\right), \operatorname{ContinuousMap}\left(K, \operatorname{Real}\left(\right)\right)\right), \\C \ge 0 \land {\forall i: I, \operatorname{IsClopen}\left(\operatorname{V}\left(i\right)\right) \land {\operatorname{map}\left(\operatorname{s}\left(i\right), p\right) = \operatorname{nu}\left(i\right) \land \operatorname{totalVariationMass}\left(\operatorname{s}\left(i\right)\right) = \operatorname{totalVariationMass}\left(\operatorname{nu}\left(i\right)\right)} \land {\operatorname{map}\left(\operatorname{t}\left(i\right), p\right) = \operatorname{nu}\left(i\right) \land \operatorname{totalVariationMass}\left(\operatorname{t}\left(i\right)\right) = \operatorname{totalVariationMass}\left(\operatorname{nu}\left(i\right)\right)}} \Rightarrow\\{\forall i: I, \operatorname{totalVariation}\left(\operatorname{nu}\left(i\right), \operatorname{compl}\left(\operatorname{V}\left(i\right)\right)\right) = 0 \land \operatorname{toReal}\left(\operatorname{totalVariationMass}\left(\operatorname{nu}\left(i\right)\right)\right) \le C} \Rightarrow\\{\forall f: \operatorname{LocallyConstant}\left(K, \operatorname{Real}\left(\right)\right), \operatorname{Eventually}\left(l, \operatorname{FibreConstantOn}\left(f, p, V\right)\right)} \Rightarrow\\\operatorname{Tendsto}\left(\operatorname{weakSignedFunctional}\left(s\right), l, \operatorname{nhds}\left(F\right)\right) \Rightarrow \operatorname{Tendsto}\left(\operatorname{weakSignedFunctional}\left(t\right), l, \operatorname{nhds}\left(F\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.arbitrary_lifts_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each index i, s(i) and t(i) push forward to the same signed measure nu(i), and both retain exactly nu(i)'s total variation mass. The variation of nu(i) gives zero mass to the complement of the clopen support V(i). Its real total variation mass is at most C, where C is nonnegative. FibreConstantOn(f,p,V) at i means literally: for all x,y in K, p(x) and p(y) belong to V(i) and p(x)=p(y) imply f(x)=f(y). For each fixed locally constant real f this condition holds eventually in l; no one stage works for every f. If the s functionals converge to F in the actual weak-star topology, the t functionals converge to the same F.

Mathlib's variation_map_le, SignedMeasure.totalVariation_eq_variation and finite-measure equality from domination and equal total mass give totalVariation(map(s,p))=map(totalVariation(s),p). This identity pulls the support concentration back to K. For a clopen test A, the compact image p[A intersect p-preimage(V)] is closed and hence measurable. Fibre constancy makes its pullback agree with A on the support. Both set differences have zero variation, so the two lifts give the same value on A. Applying this to all inverse images of a locally constant f makes the actual signed pushforwards along f equal. Mathlib's signed vector integral_map then gives equality of the f integrals.

The locally constant algebra separates points on K. The existing real Stone–Weierstrass theorem supplies a locally constant g within epsilon/(2C+2) of an arbitrary continuous f. Once the two g integrals agree, the integral difference for f is at most 2C times the uniform approximation error. This tends to zero, including C=0. Adding the vanishing difference to the reference evaluation limit proves convergence on every continuous test; the existing weak-dual evaluation criterion gives the conclusion.

Repository search found no exact all-lifts signed-measure convergence theorem in the topology or total-variation owners. The pinned Mathlib suppliers are reused directly rather than reproved. The new synthesis supplies the all-choices quantifier needed in the ordinary signed-measure condition (F) of the Talagrand candidate. It proves stability for any already given norm-preserving lifts; it does not construct lifts or prove their existence by Hahn–Banach or Riesz representation. It does not formalize the transfinite recursion, CH bookkeeping, Banach-space preservation theorem or Problem 8.2. No literature novelty or official acceptance of that problem is asserted.

**Theorem 1.7 (Signed integration under continuous pushforward).**

Lean statement: `D5/S3/Topology/Measures/NormPreservingLifts.functional_map`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/NormPreservingLifts.functional_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary compact Borel source X and compact Borel target Y, every signed measure s, continuous p from X to Y and real continuous g on Y satisfy signedFunctional(s.map p)(g) = signedFunctional(s)(g composed with p). No Hausdorff, nonempty or injective-map premise is added. This is the existing private historical-capture integral-map supplier moved to its natural shared owner; historical capture and compact-family variation loss both consume it. The proof uses native vector integral_map and compact-source integrability.

## References

- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.apply_eq_of_supported_clopen`
- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.arbitrary_lifts_tendsto`
- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.functional_map`
- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.signedFunctional_norm_le`
- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.signedFunctional_sub_toSignedMeasure`
- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.totalVariation_map_of_mass`
- Truth anchor: `D5/S3/Topology/Measures/NormPreservingLifts.totalVariation_sub_toSignedMeasure_le`
