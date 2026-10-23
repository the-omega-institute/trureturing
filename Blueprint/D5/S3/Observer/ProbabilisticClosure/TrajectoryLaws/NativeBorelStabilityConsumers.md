# Original supported risk, zero face and necessary repairs

## Abstract

Original supported risk, zero face and necessary repairs.

DepthPMF is any probability mass function on positive natural depths; the two positivity predicates mean mu(1)!=0 and mu(2)!=0. Exactly the original DepthLaw.rate(k) targets are retained. supportedRisk(nu,mu) is max over p,beta of the real supremum over every k with mu(k)!=0 of the complete-configuration mean TV to native(s,rate(k)), minus radius(s). radius(p)=1116529/22781250 and radius(beta)=239/6750. Every target loss is measurable and lies in [0,1], so the real supported supremum is bounded; supported endpoints make it nonempty. rate(1)=1/3 and rate(2)=2/5 are exact Fibonacci evaluations.

PhaseMargins means a phase-indexed family of measures on RegularDescriptor(s); probabilityMargins requires probability at both phases. UnboxedCommonFlow carries exactly the original CommonFlow law, joint-flow, disintegration, unweighted margin and full normalized-residual fields, omitting only boxP and boxB. unboxedMargins and flowMargins select those same original margins. zeroFace(U,mu) fills only the two proved box fields after zero risk; it retains U's actual laws, kernels, joint flows and all marginal and residual equations.

The coordinate triangle slack is |D{t}-P_a{t}|+|D{t}-P_b{t}|-|P_a{t}-P_b{t}|. Singleton removal or insertion in the complete endpoint sign event bounds it by twice the full TV triangle slack. At zero supported risk, endpoint budgets force the nonnegative integrated TV slack, hence each coordinate slack, to vanish. Countability synchronizes every coordinate, including infinity, and equality in the real absolute-value triangle yields EndpointBox. This argument assumes no boxes at its input.

pEventMean(F)=integral Q(Ep).toReal dnuP; pMeanLoss is integral fullLoss(p,b) dnuP. The boxed p midpoint is the separate value 11758471/22781250. It imposes neither a suspended midpoint nor all-supported budgets. For a proposed repair delta is the difference of its corrected meanCoordinate from (4/9)(2/9)^n. The two NULL155 p laws have this common native lower tail for n>=5; the repair theorem is a necessary condition on a single actually compatible repaired pair, not on its retained finite features.

**Theorem 1.1 (The unchanged all-supported risk bound).**

$$\forall F: CommonFlow, \forall mu: DepthPMF, \forall b: Bool, \forall n: Nat, ((\operatorname{positiveDepthOne}\left(mu\right))\land(\operatorname{positiveDepthTwo}\left(mu\right)))\Rightarrow((4\leq n)\Rightarrow(\operatorname{radiusP}\left(\right)\leq \operatorname{supportedRisk}\left(\operatorname{flowMargins}\left(F\right), mu\right)+{\operatorname{HR}\left(b\right)} \cdot {\frac{\operatorname{slack}\left(F, b, n\right)}{{\operatorname{cR}\left(b\right)} \cdot {{\operatorname{zR}\left(b\right)}^{n}}}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.original_risk_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The opposite endpoint remains one original supported target in the full supremum. Complete configuration TV triangle and integration give radius(p)<=J+completeLoss. Apply normalized_stability for both endpoints and all n>=4.

**Theorem 1.2 (Zero supported excess proves full boxes).**

$$\forall nu: PhaseMargins, \forall mu: DepthPMF, \forall s: ActivePhase, (\operatorname{probabilityMargins}\left(nu\right))\Rightarrow(((\operatorname{positiveDepthOne}\left(mu\right))\land(\operatorname{positiveDepthTwo}\left(mu\right)))\Rightarrow((\operatorname{supportedRisk}\left(nu, mu\right)=0)\Rightarrow(\operatorname{AE}\left(\operatorname{margin}\left(nu, s\right), D, \operatorname{EndpointBox}\left(D\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.zero_face_boxes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative coordinate slack has zero integral at every complete atom under the original arbitrary Borel probability margin. AE zero and countability yield all full endpoint intervals. Neither normalized residuals nor preassumed boxes are used in this implication.

**Theorem 1.3 (Each p endpoint loss at the separate midpoint).**

$$\forall F: CommonFlow, \forall b: Bool, (\operatorname{pEventMean}\left(F\right)=\frac{11758471}{22781250})\Rightarrow(\operatorname{pMeanLoss}\left(F, b\right)=\operatorname{radiusP}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.boxed_p_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full Ep TV formula integrates to radius(p) at each endpoint. No suspended midpoint or supported nonendpoint budget is inferred.

**Theorem 1.4 (Both mean bounds at the separate midpoint).**

$$\forall F: CommonFlow, \forall n: Nat, (\operatorname{pEventMean}\left(F\right)=\frac{11758471}{22781250})\Rightarrow((4\leq n)\Rightarrow(({{\frac{4}{9}} \cdot {{\frac{2}{9}}^{n}}} \cdot {1+\frac{\operatorname{radiusP}\left(\right)}{\frac{9839648}{2657205}}}\leq \operatorname{meanCoordinate}\left(F, n\right))\land(\operatorname{meanCoordinate}\left(F, n\right)\leq {{\frac{9}{25}} \cdot {{\frac{6}{25}}^{n}}} \cdot {1-\frac{\operatorname{radiusP}\left(\right)}{\frac{20723912}{5859375}}})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.midpoint_mean_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each p endpoint mean loss lower-bounds completeLoss by radius(p). Normalize the two stability estimates and substitute the two slack definitions on the same meanCoordinate.

**Theorem 1.5 (Both mean bounds from unboxed zero risk).**

$$\forall U: UnboxedCommonFlow, \forall mu: DepthPMF, \forall n: Nat, ((\operatorname{positiveDepthOne}\left(mu\right))\land(\operatorname{positiveDepthTwo}\left(mu\right)))\Rightarrow((\operatorname{supportedRisk}\left(\operatorname{unboxedMargins}\left(U\right), mu\right)=0)\Rightarrow((4\leq n)\Rightarrow(({{\frac{4}{9}} \cdot {{\frac{2}{9}}^{n}}} \cdot {1+\frac{\operatorname{radiusP}\left(\right)}{\frac{9839648}{2657205}}}\leq \operatorname{meanCoordinate}\left(\operatorname{zeroFace}\left(U, mu\right), n\right))\land(\operatorname{meanCoordinate}\left(\operatorname{zeroFace}\left(U, mu\right), n\right)\leq {{\frac{9}{25}} \cdot {{\frac{6}{25}}^{n}}} \cdot {1-\frac{\operatorname{radiusP}\left(\right)}{\frac{20723912}{5859375}}}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.zero_face_mean_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

zeroFace constructs the boxed CommonFlow from the same unboxed pair. The original risk triangle at J=0 gives the loss lower bound, and normalized stability yields the simultaneous interval for its unchanged coordinate mean.

**Theorem 1.6 (Necessary repair on the separate midpoint face).**

$$\forall F: CommonFlow, \forall n: Nat, \forall delta: Real, (\operatorname{pEventMean}\left(F\right)=\frac{11758471}{22781250})\Rightarrow((5\leq n)\Rightarrow((\operatorname{meanCoordinate}\left(F, n\right)={\frac{4}{9}} \cdot {{\frac{2}{9}}^{n}}+delta)\Rightarrow(({\frac{{\frac{4}{9}} \cdot {\operatorname{radiusP}\left(\right)}}{\frac{9839648}{2657205}}} \cdot {{\frac{2}{9}}^{n}}\leq delta)\land(0<delta))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.midpoint_repair_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corrected mean equation identifies delta with the lower signed slack. The lower normalized correction implies the decaying positive floor for every n>=5.

**Theorem 1.7 (Necessary repair on the original zero-risk face).**

$$\forall U: UnboxedCommonFlow, \forall mu: DepthPMF, \forall n: Nat, \forall delta: Real, ((\operatorname{positiveDepthOne}\left(mu\right))\land(\operatorname{positiveDepthTwo}\left(mu\right)))\Rightarrow((\operatorname{supportedRisk}\left(\operatorname{unboxedMargins}\left(U\right), mu\right)=0)\Rightarrow((5\leq n)\Rightarrow((\operatorname{meanCoordinate}\left(\operatorname{zeroFace}\left(U, mu\right), n\right)={\frac{4}{9}} \cdot {{\frac{2}{9}}^{n}}+delta)\Rightarrow(({\frac{{\frac{4}{9}} \cdot {\operatorname{radiusP}\left(\right)}}{\frac{9839648}{2657205}}} \cdot {{\frac{2}{9}}^{n}}\leq delta)\land(0<delta)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.zero_face_repair_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-face construction preserves the original pair. Its lower correction gives the same decaying positive floor, even when the proposed repaired pair varies with the return index.

These bounds construct no feasible or operational pair and determine no general positive risk gap. They supply no finite representation, exact sampler, installed source-independent program or paid acquisition. The original common depth, both accepted seeds, every paid rejection, partial parse and return, complete record including noncompletion, identical acquired and synthetic updates, matching Stop and all COMPLETE charges retain their source meaning. No additional observation port, reset or source-depth draw is introduced.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.boxed_p_midpoint`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.midpoint_mean_interval`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.midpoint_repair_floor`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.original_risk_normalized`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.zero_face_boxes`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.zero_face_mean_interval`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers.zero_face_repair_floor`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability](NativeBorelNormalizedStability.md)
