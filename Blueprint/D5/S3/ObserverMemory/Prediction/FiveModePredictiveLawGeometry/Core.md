# Five Mode Predictive Law Geometry Core

## Abstract

Finite-horizon mixture geometry and exact startup cutoffs of the actual five-mode source.

The literal five-state source has visible symbols Fin 4, with B as code 2. Admissibility is p>0, q>0, r>0 and p+q+r<1. Write a=1-p-q, b=1-r and c=1-p-q-r. Pure and empty laws are the actual future and initial word laws of FiniteStartFiveModeSource. LawProfile contains every finite horizon. ProbabilityProfile requires nonnegative weights of total mass one; CoherentProfile also requires consistency under deleting the final read.

Finite total variation is half the sum of absolute mass differences; profileDistance is its supremum over finite horizons. mixtureLaw x combines pure laws 2 and 4 with weights x and 1-x. Finite TV holds for real signed coordinates; probability and supremum statements restrict coordinates to [0,1].

For unequal a and b, theta=min(a,b)/max(a,b), minority theta k=theta^k/(1+theta^k), and orientedMixture z puts weight z on the minority branch. The acquired startup word is B^(k+1). cutoff t e is the natural ceiling of log((1-e)/e)/abs(log t), and N2=cutoff theta (2 epsilon). The first accepted index uses a non-strict inequality, including exact ties.

**Theorem 1.1 (Literal all-B holding masses).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall H: \mathbb{N},\ (\operatorname{word}\left(\operatorname{pureLaw}\left(p, q, r, 2\right), H, \operatorname{constant}\left(B\right)\right) = (\operatorname{a}\left(p, q\right))^{H} \land \operatorname{word}\left(\operatorname{pureLaw}\left(p, q, r, 4\right), H, \operatorname{constant}\left(B\right)\right) = (\operatorname{b}\left(r\right))^{H})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.branch_all_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both masses are powers at every finite horizon, including H=0.

**Theorem 1.2 (Exact common branch support).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall H: \mathbb{N},\ (\forall w: \operatorname{Fin}\left(H\right)\to Visible,\ ((0 < \operatorname{word}\left(\operatorname{pureLaw}\left(p, q, r, 2\right), H, w\right) \land 0 < \operatorname{word}\left(\operatorname{pureLaw}\left(p, q, r, 4\right), H, w\right)) \iff w = \operatorname{constant}\left(B\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.branch_word_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first exit categories are disjoint, so the common positive support is exactly the all-B word.

**Theorem 1.3 (Finite branch total variation).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall H: \mathbb{N},\ \operatorname{TV}\left(\operatorname{at}\left(\operatorname{pureLaw}\left(p, q, r, 2\right), H\right), \operatorname{at}\left(\operatorname{pureLaw}\left(p, q, r, 4\right), H\right)\right) = (1-(\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right))^{H}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.branch_finite_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite value is 1-min(a,b)^H. Its horizon dependence is retained.

**Theorem 1.4 (Finite mixture total variation).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall x: \mathbb{R},\ (\forall z: \mathbb{R},\ (\forall H: \mathbb{N},\ \operatorname{TV}\left(\operatorname{at}\left(\operatorname{mixtureLaw}\left(p, q, r, x\right), H\right), \operatorname{at}\left(\operatorname{mixtureLaw}\left(p, q, r, z\right), H\right)\right) = (\operatorname{abs}\left((x-z)\right)*(1-(\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right))^{H})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.mixture_finite_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Homogeneity of the signed difference combines with the actual branch overlap.

**Theorem 1.5 (The all-horizon mixture metric).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall x: \mathbb{R},\ (\forall z: \mathbb{R},\ ((x \in \operatorname{Icc}\left(0, 1\right) \land z \in \operatorname{Icc}\left(0, 1\right)) \Rightarrow \operatorname{profileDistance}\left(\operatorname{mixtureLaw}\left(p, q, r, x\right), \operatorname{mixtureLaw}\left(p, q, r, z\right)\right) = \operatorname{abs}\left((x-z)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.mixture_profile_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite holding powers tend to zero, so the supremum equals the coordinate distance.

**Theorem 1.6 (Positive uniform separation constant).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow 0 < \operatorname{kappa}\left(p, q, r\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.kappa_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

kappa is min(c,p,q,a,c*s/(s+r),a*p/s,a*q/s,1/25), with every term strictly positive.

**Theorem 1.7 (Singleton versus any mixture).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall x: \mathbb{R},\ (x \in \operatorname{Icc}\left(0, 1\right) \Rightarrow (\forall j: State,\ ((j = 0 \lor (j = 1 \lor j = 3)) \Rightarrow \operatorname{kappa}\left(p, q, r\right) \leq \operatorname{profileDistance}\left(\operatorname{pureLaw}\left(p, q, r, j\right), \operatorname{mixtureLaw}\left(p, q, r, x\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.singleton_mixture_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate and finite-event estimates apply without generic-parameter exclusions.

**Theorem 1.8 (Empty versus any mixture).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall x: \mathbb{R},\ (x \in \operatorname{Icc}\left(0, 1\right) \Rightarrow \frac{1}{25} \leq \operatorname{profileDistance}\left(\operatorname{emptyLaw}\left(p, q, r\right), \operatorname{mixtureLaw}\left(p, q, r, x\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.empty_mixture_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two one-step event gaps give the universal lower bound one twenty-fifth.

**Theorem 1.9 (Strict geometric monotonicity).**

$$(\forall t: \mathbb{R},\ ((0 < t \land t < 1) \Rightarrow \operatorname{StrictAnti}\left(\operatorname{minority}\left(t\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.minority_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite startup minority coordinate decreases at every step when 0<t<1.

**Theorem 1.10 (Geometric decay).**

$$(\forall t: \mathbb{R},\ ((0 < t \land t < 1) \Rightarrow \operatorname{Tendsto}\left(\operatorname{minority}\left(t\right), atTop, \operatorname{nhds}\left(0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.minority_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The limit concerns finite startup coordinates, not an observed infinite history.

**Theorem 1.11 (Exact first non-strict cutoff and ties).**

$$(\forall t: \mathbb{R},\ (\forall e: \mathbb{R},\ (((0 < t \land t < 1) \land (0 < e \land e < \frac{1}{2})) \Rightarrow (0 < \operatorname{cutoff}\left(t, e\right) \land (\operatorname{minority}\left(t, \operatorname{cutoff}\left(t, e\right)\right) \leq e \land ((\forall i: \mathbb{N},\ (i < \operatorname{cutoff}\left(t, e\right) \Rightarrow e < \operatorname{minority}\left(t, i\right))) \land ((\forall k: \mathbb{N},\ (\operatorname{minority}\left(t, k\right) \leq e \iff \operatorname{cutoff}\left(t, e\right) \leq k)) \land (\operatorname{minority}\left(t, \operatorname{cutoff}\left(t, e\right)\right) = e \iff \frac{\operatorname{log}\left(\frac{(1-e)}{e}\right)}{\operatorname{abs}\left(\operatorname{log}\left(t\right)\right)} = \operatorname{castReal}\left(\operatorname{cutoff}\left(t, e\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.cutoff_first_nonstrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal natural ceiling is positive, accepts equality at the threshold, and excludes all earlier indices.

**Theorem 1.12 (The actual acquired startup law).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall k: \mathbb{N},\ (\forall H: \mathbb{N},\ (\forall w: \operatorname{Fin}\left(H\right)\to Visible,\ \operatorname{word}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), H, w\right) = \operatorname{word}\left(\operatorname{orientedMixture}\left(p, q, r, \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), k\right)\right), H, w\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.actual_oriented_startup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The acquired all-B posterior from the literal source gives G_delta at every future word.

**Theorem 1.13 (The source-specific minority cutoff).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (0 < \operatorname{N2}\left(p, q, r, epsilon\right) \land (\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, epsilon\right)\right) \leq (2*epsilon) \land ((\forall i: \mathbb{N},\ (i < \operatorname{N2}\left(p, q, r, epsilon\right) \Rightarrow (2*epsilon) < \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), i\right))) \land ((\forall k: \mathbb{N},\ (\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), k\right) \leq (2*epsilon) \iff \operatorname{N2}\left(p, q, r, epsilon\right) \leq k)) \land (\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, epsilon\right)\right) = (2*epsilon) \iff \frac{\operatorname{log}\left(\frac{(1-(2*epsilon))}{(2*epsilon)}\right)}{\operatorname{abs}\left(\operatorname{log}\left(\operatorname{theta}\left(p, q, r\right)\right)\right)} = \operatorname{castReal}\left(\operatorname{N2}\left(p, q, r, epsilon\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.actual_startup_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both unequal orientations have the same exact minority threshold index N2.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.actual_oriented_startup`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.actual_startup_cutoff`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.branch_all_B`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.branch_finite_tv`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.branch_word_overlap`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.cutoff_first_nonstrict`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.empty_mixture_separation`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.kappa_positive`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.minority_strictAnti`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.minority_tendsto_zero`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.mixture_finite_tv`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.mixture_profile_distance`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core.singleton_mixture_separation`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource](../FiniteStartFiveModeSource.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../../TotalVariation/Metric.md)
