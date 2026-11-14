# Positive Words, Ready Return and Continuous Ray Descent

## Abstract

Positive statistical return and sequential ready return yield a continuous full-row response.

The word domain W is List(Fin 11), with chronological concatenation: act(a++b,P)=act(b,act(a,P)). A Law is an arbitrary real function p on all these words with 0<=p(a)<=1. Coordinates are Option W with the discrete topology. The none coordinate is star and is always one; some [] is the empty terminal future and equals p(a). The row x(a) is the bounded continuous function (1,(p(a++f)) for every f in W), with its full supremum norm. V is the real algebraic span of all rows, and Vhat=closedSpan is its norm closure in this Banach space. No dimension or closedness hypothesis on V occurs.

Geometry R means a metric space R, eleven maps gate(j):R->R, each an isometry with tenth iterate equal to the identity at every point, and one ready point. act is chronological iteration and ray(a)=act(a,ready). Density means DenseRange ray on this same metric space. Compactness is required only in the backward represented-statistics argument. Rten is the statistical equality p(a++j^10++f)=p(a++f) for every a,j,f. ReadyReturn is sequential convergence of full rows to the empty row whenever a sequence of actual word rays converges to the ready ray; it is not pointwise convergence at each fixed future.

**Theorem 1.1 (The same positive inverse transports both rows).**

$$\forall L:\operatorname{Law}\left(\right),\ \operatorname{Rten}\left(L\right) \Rightarrow \forall a:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \forall b:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \operatorname{dist}\left(\operatorname{row}\left(L, a\right), \operatorname{row}\left(L, b\right)\right)=\operatorname{dist}\left(\operatorname{row}\left(L, \operatorname{append}\left(a, \operatorname{inverseWord}\left(b\right)\right)\right), \operatorname{row}\left(L, \operatorname{nil}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PositiveWordRayDescent.row_return_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

inverseWord reverses the address order and replaces each address by nine positive copies. Statistical Rten cancels b++inverseWord(b) between every prefix and every future. Appending any word is a contraction on row differences because it restricts the future coordinates. Appending its positive inverse recovers the original difference, so the contraction is an isometry on these row pairs. In particular x(b++inverseWord(b))=x([]), and simultaneous transport gives the displayed identity. Geometry plays no part in this statistical proof. This identity does not equate program histories or provide a physical inverse service.

**Theorem 1.2 (Sequential return controls all pairs and noninjective fibers).**

$$\forall R:\operatorname{Type}\left(\right),\ \forall L:\operatorname{Law}\left(\right),\ \forall G:\operatorname{Geometry}\left(R\right),\ \operatorname{MetricSpace}\left(R\right) \land \operatorname{Rten}\left(L\right) \land \operatorname{ReadyReturn}\left(L, G\right) \Rightarrow (\forall epsilon:\operatorname{Real}\left(\right),\ 0<epsilon \Rightarrow \exists delta:\operatorname{Real}\left(\right),\ 0<delta \land \forall a:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \forall b:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \operatorname{dist}\left(\operatorname{ray}\left(G, a\right), \operatorname{ray}\left(G, b\right)\right)<delta \Rightarrow \operatorname{dist}\left(\operatorname{row}\left(L, a\right), \operatorname{row}\left(L, b\right)\right)<epsilon) \land \forall a:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \forall b:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \operatorname{ray}\left(G, a\right)=\operatorname{ray}\left(G, b\right) \Rightarrow \operatorname{row}\left(L, a\right)=\operatorname{row}\left(L, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PositiveWordRayDescent.uniform_rows_and_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an epsilon bound failed at ready, choose a violating actual word c(n) whose ray distance is less than 1/(n+1). These rays converge to ready, while their full row distances stay at least epsilon, contradicting the sequential premise. For arbitrary a,b, append inverseWord(b) to both. Statistical transport preserves their row distance. The same positive word acts isometrically on both rays and returns ray(b) to ready, by the independent tenth-order geometry. Thus one ready bound controls all actual pairs. Applying every positive epsilon to an equal-ray pair makes its row distance zero. The word map is never assumed injective.

**Theorem 1.3 (Unique full-row extension into the closed span).**

$$\forall R:\operatorname{Type}\left(\right),\ \forall L:\operatorname{Law}\left(\right),\ \forall G:\operatorname{Geometry}\left(R\right),\ \operatorname{MetricSpace}\left(R\right) \land \operatorname{DenseRange}\left(\operatorname{ray}\left(G\right)\right) \land \operatorname{Rten}\left(L\right) \land \operatorname{ReadyReturn}\left(L, G\right) \Rightarrow \exists \phi:\operatorname{ContinuousMap}\left(R, \operatorname{closedSpan}\left(L\right)\right),\ \operatorname{Descent}\left(L, G, \phi\right) \land \forall x:\operatorname{ContinuousMap}\left(R, \operatorname{closedSpan}\left(L\right)\right),\ \operatorname{Descent}\left(L, G, x\right) \Rightarrow x=\phi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PositiveWordRayDescent.continuous_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a unique continuous Phi:R->Vhat satisfying all four conditions: Phi(ray(a))=x(a) for every word; Phi(P)(none)=1; every Phi(P)(some f) belongs to [0,1]; and Phi(P)(some f)=Phi(act(f,P))(some []) for every P and every original future f. Descent in the formula denotes exactly this conjunction. In particular q(P)=Phi(P)(some []) is continuous, takes values in [0,1], and represents p at every actual ray.

First apply uniform_rows_and_fibers. Choose a representing word only on range(ray); fiber constancy makes the chosen row independent of that word, and the pair estimate makes this map uniformly continuous in the inherited ray metric. Mathlib Dense.uniformContinuous_extend extends it into the complete bounded-row space. The closed span contains every row, so dense induction places every extension value in Vhat; the map is then lifted into that closed subtype. Continuous coordinate evaluation extends normalization and bounds. For each f, both coordinate evaluation and evaluation after act(f) are continuous and agree on the dense actual rays, which proves the full future formula. The same dense equalizer proves uniqueness. The raw word-to-ray map need not be a uniform embedding.

**Theorem 1.4 (A continuous representation supplies both statistical premises).**

$$\forall R:\operatorname{Type}\left(\right),\ \forall L:\operatorname{Law}\left(\right),\ \forall G:\operatorname{Geometry}\left(R\right),\ \operatorname{MetricSpace}\left(R\right) \land \operatorname{CompactSpace}\left(R\right) \Rightarrow \forall q:\operatorname{ContinuousMap}\left(R, \operatorname{Icc}\left(0, 1\right)\right),\ (\forall a:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \operatorname{q}\left(\operatorname{ray}\left(G, a\right)\right)=\operatorname{probability}\left(L, a\right)) \Rightarrow \operatorname{Rten}\left(L\right) \land \operatorname{ReadyReturn}\left(L, G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PositiveWordRayDescent.represented_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume q is a continuous [0,1]-valued response representing all actual p(a). Compactness gives uniform continuity of its real coordinate. A half-epsilon bound applies simultaneously after every future because act(f) is an isometry. BoundedContinuousFunction.dist_le gives a full supremum bound, then the strict half-epsilon margin proves ReadyReturn. The same assumed representation transfers the geometric tenth-order identity to every statistical prefix/future equality. Gate order by itself is not a premise about an unknown terminal law.

**Theorem 1.5 (Capacity-free return and a unique continuous response are equivalent).**

$$\forall R:\operatorname{Type}\left(\right),\ \forall L:\operatorname{Law}\left(\right),\ \forall G:\operatorname{Geometry}\left(R\right),\ \operatorname{MetricSpace}\left(R\right) \land \operatorname{DenseRange}\left(\operatorname{ray}\left(G\right)\right) \land \operatorname{CompactSpace}\left(R\right) \Rightarrow (\operatorname{Rten}\left(L\right) \land \operatorname{ReadyReturn}\left(L, G\right)) \Leftrightarrow \exists q:\operatorname{ContinuousMap}\left(R, \operatorname{Icc}\left(0, 1\right)\right),\ (\forall a:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \operatorname{q}\left(\operatorname{ray}\left(G, a\right)\right)=\operatorname{probability}\left(L, a\right)) \land \forall r:\operatorname{ContinuousMap}\left(R, \operatorname{Icc}\left(0, 1\right)\right),\ (\forall a:\operatorname{List}\left(\operatorname{Fin}\left(11\right)\right),\ \operatorname{r}\left(\operatorname{ray}\left(G, a\right)\right)=\operatorname{probability}\left(L, a\right)) \Rightarrow r=q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PositiveWordRayDescent.ready_return_iff_unique_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For compact R and dense actual ready orbit, Rten and ReadyReturn hold if and only if there exists exactly one continuous q:R->[0,1] representing all p(a). The forward proof consumes continuous_descent and evaluates some []; the backward proof consumes represented_statistics. Equality on the same dense rays gives uniqueness. The constant law p=1/3 has star coordinate one and empty-future coordinate 1/3, so the two coordinates cannot be interchanged.

**Theorem 1.6 (Return, pair and scalar suprema agree exactly).**

$$\forall R:\operatorname{Type}\left(\right),\ \forall L:\operatorname{Law}\left(\right),\ \forall G:\operatorname{Geometry}\left(R\right),\ \operatorname{MetricSpace}\left(R\right) \land \operatorname{Rten}\left(L\right) \Rightarrow \forall s:\operatorname{Real}\left(\right),\ 0\le s \Rightarrow \operatorname{sSup}\left(\operatorname{returnErrors}\left(L, G, s\right)\right)=\operatorname{sSup}\left(\operatorname{pairErrors}\left(L, G, s\right)\right) \land \operatorname{sSup}\left(\operatorname{pairErrors}\left(L, G, s\right)\right)=\operatorname{sSup}\left(\operatorname{scalarErrors}\left(L, G, s\right)\right) \land \operatorname{Member}\left(\operatorname{sSup}\left(\operatorname{returnErrors}\left(L, G, s\right)\right), \operatorname{Icc}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PositiveWordRayDescent.three_moduli_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s>=0, returnErrors consists of distances Delta(c,[]) with ray distance at most s; pairErrors consists of Delta(a,b) under the pair ray-distance constraint; scalarErrors consists of |p(a)-p(b)| under that same constraint. All three sets contain zero and are bounded above by one. Their real suprema are equal, and the return supremum lies in [0,1]. No supremum is assumed attained. This includes every source value 0<=s<=1 and the endpoint s=0.

Pair candidates transport to return candidates by the same reverse-nine word, preserving the constraint. Return candidates are pair candidates with the second word empty. Empty-future evaluation bounds scalar error by row error. Conversely every common future gives a scalar candidate at the same ray distance, by isometry; bounding every coordinate by the scalar supremum bounds the whole row distance. The proof uses le_csSup and csSup_le only after explicit nonemptiness and boundedness. ReadyReturn and compactness are unnecessary for this equality.

## Original native application and remaining geometric correspondence

The intended source is VII24.1-25.1 with III150.1 geometry and VII10.1/17.1 conventions. Its native specialization is R=the pure rays of the original V12^1, complex dimension 89, with d(P,Q)=operatorNorm(P-Q); gate(j) is conjugation by the same original K_j; ready is P_(e0) with e0=R0 v; p(a) is the unknown actual event probability for A={b1=1}. Every eleven-address positive history and every terminal future is retained. The 26-dimensional J(H tensor C^2) code and all 63 complementary dimensions, J itself, the phase/address convention, ordinary causal normalization and original ideal, finite-supply, reliability and cost contracts keep their original meanings. Geometry and density are inputs from the paper, never deductions from statistical Rten.

This metric-geometry theorem does not yet instantiate that original carrier. WeightedLegalPathTemperleyLieb.LegalPath/pathProjection and WeightedPathArtinRepresentation.rho/rhoUnit supply reusable path and generator algebra, but a typed equality with the original V12^1, all eleven normalized gates, e0, J and Q is still required. RankOneContextCommutator.IsNormalizedRankOneProjection is algebraic; it does not provide the compact operator-norm ray space. The further obligations are the faithful normalized-projector metric/compactness bridge, original gate unitarity and tenth-order phase specialization, and DenseRange of the same actual ready rays while preserving the full PU(89) density assumption. No arbitrary Fin 89 matrix family or different NativeProtocol is identified with those native objects.

The intended path parameters are the two labels Bool, with true denoting vacuum, adjacency excluding two consecutive true labels, d(true)=1, d(false)=phi and delta=phi. The n=12 true-to-true block has the literal boundary form (1,0,b1,...,b9,0,1), with no adjacent occupied internal bits. The required source correspondence sends this full path block to the original basis; the original extra right boundary bit remains fixed at zero. This parameter assignment specifies a concrete correspondence to prove, not a completed Lean equivalence. With A=exp(2*pi*i/5), the original phase convention calls for K_j=-rho_j on that same block; verifying the parameter equation, projection entries and this phase identity is part of the unpaid native gate bridge.

The result supplies the analytic return/descent predecessor needed by the closed native consumer in Quantum VI89.9. The entire fixed native theorem remains conditional on those native bridges. The full-span linear operator formulation of VII24.2 is separate from the row-distance transport proved here. No Born classification, predictive capacity, finite separating future family, physical inverse availability or change to the original program domain follows from this unit. Generic bounded-function construction, coordinate evaluation and dense extension are direct Mathlib applications; the new inference is the positive-word passage from sequential ready return to global row consistency and its continuous descent consumer.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PositiveWordRayDescent.continuous_descent`
- Truth anchor: `D5/S3/Quantum/Algebra/PositiveWordRayDescent.ready_return_iff_unique_response`
- Truth anchor: `D5/S3/Quantum/Algebra/PositiveWordRayDescent.represented_statistics`
- Truth anchor: `D5/S3/Quantum/Algebra/PositiveWordRayDescent.row_return_transport`
- Truth anchor: `D5/S3/Quantum/Algebra/PositiveWordRayDescent.three_moduli_equal`
- Truth anchor: `D5/S3/Quantum/Algebra/PositiveWordRayDescent.uniform_rows_and_fibers`
