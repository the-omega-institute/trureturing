# Five Mode Predictive Law Geometry

## Abstract

Finite-horizon geometry and exact startup cutoffs of the actual five-mode source.

The source has states Fin 5, visible symbols Fin 4, and B is visible code 2. Its transition and observation are those of FiniteStartFiveModeSource. Admissibility is p>0, q>0, r>0 and p+q+r<1. Put s=p+q, a=1-s, b=1-r and c=1-s-r. These conditions include p=q and r=p+q. Every pure law is the actual source futureWordWeight from its point mass. The empty law is initialWordWeight from the uniform initial vector and predicts Y0.

LawProfile is the dependent family of real word weights on Fin H to Visible, for every natural H. ProbabilityProfile means nonnegative entries and total mass one at each H. CoherentProfile adds pointwise consistency under deleting the final read. TV is the finite half-sum of absolute mass differences. profileDistance is its supremum over finite horizons; H=0 contributes zero for probability profiles. mixtureLaw x is x times pureLaw 2 plus 1-x times pureLaw 4. The finite TV identity also holds for real signed mixture coordinates; probability and supremum claims below restrict them to [0,1].

FirstExit true selects a first non-B symbol 0; FirstExit false selects a first non-B symbol in {1,3}. exitMass sums this event in a finite word. firstBExitMass F n z sums words of horizon n+1 beginning with B whose remaining n symbols have FirstExit z. Thus at horizon H>=1 the displayed powers use n=H-1. These are finite cylinders, with no conditioning on an infinite all-B history.

On unequal holding probabilities theta=min(a,b)/max(a,b). minority theta k is theta^k/(1+theta^k). orientedMixture z is mixtureLaw (1-z) when a>b and mixtureLaw z otherwise. dominantLaw is pureLaw 2 when a>b and pureLaw 4 otherwise. cutoff t e is the natural ceiling of log((1-e)/e)/abs(log t), using the natural logarithm; N2 is cutoff theta (2 epsilon). actualStartupLaw k denotes the actual law after B^(k+1); actualStartupDistance k is its profileDistance from dominantLaw. The actual startup index k belongs to the acquired word B^(k+1). The equality r=p+q is treated by the half-mixture statements.

cappedClassLaw has mathematical labels State+Fin L: a pure label denotes its pure law and a startup label k denotes the actual law after B^(k+1). fixedClassLaw has labels State+Unit and denotes the one startup law after B^L. OptionCase uses the empty law at None and the given class law at Some. These label families classify the stated history domains. They do not provide a recording length to an autonomous update. PostreadLawSet and InitializedLawSet are images of actual positive histories, excluding or including the empty history respectively.

**Theorem 1.1 (One coherent family and both exact geometries).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall x: \mathbb{R},\ (\forall z: \mathbb{R},\ ((x \in \operatorname{Icc}\left(0, 1\right) \land z \in \operatorname{Icc}\left(0, 1\right)) \Rightarrow (\operatorname{CoherentProfile}\left(\operatorname{mixtureLaw}\left(p, q, r, x\right)\right) \land ((\forall H: \mathbb{N},\ \operatorname{TV}\left(\operatorname{at}\left(\operatorname{mixtureLaw}\left(p, q, r, x\right), H\right), \operatorname{at}\left(\operatorname{mixtureLaw}\left(p, q, r, z\right), H\right)\right) = (\operatorname{abs}\left((x-z)\right)*(1-(\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right))^{H}))) \land \operatorname{profileDistance}\left(\operatorname{mixtureLaw}\left(p, q, r, x\right), \operatorname{mixtureLaw}\left(p, q, r, z\right)\right) = \operatorname{abs}\left((x-z)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.coherent_mixture_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite laws are normalized, nonnegative and consistent under deletion of the last read.

**Theorem 1.2 (Finite first-exit probabilities).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall H: \mathbb{N},\ (\operatorname{exitMass}\left(\operatorname{pureLaw}\left(p, q, r, 2\right), H, true\right) = 0 \land (\operatorname{exitMass}\left(\operatorname{pureLaw}\left(p, q, r, 4\right), H, true\right) = (1-(\operatorname{b}\left(r\right))^{H}) \land (\operatorname{exitMass}\left(\operatorname{pureLaw}\left(p, q, r, 2\right), H, false\right) = (1-(\operatorname{a}\left(p, q\right))^{H}) \land \operatorname{exitMass}\left(\operatorname{pureLaw}\left(p, q, r, 4\right), H, false\right) = 0))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.branch_exit_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected first exit is measured within each finite word, before any later source motion.

**Theorem 1.3 (The two empty-law cylinder masses).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall H: \mathbb{N},\ (\operatorname{firstBExitMass}\left(\operatorname{emptyLaw}\left(p, q, r\right), H, true\right) = \frac{(1-(\operatorname{b}\left(r\right))^{H})}{5} \land \operatorname{firstBExitMass}\left(\operatorname{emptyLaw}\left(p, q, r\right), H, false\right) = \frac{(1-(\operatorname{a}\left(p, q\right))^{H})}{5}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.empty_first_B_exit_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At horizon H+1 the masses are (1-b^H)/5 and (1-a^H)/5. Equivalently their exponent is H-1 at positive total horizon H.

**Theorem 1.4 (A pure start forbids one exit category).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall i: State,\ ((\forall H: \mathbb{N},\ \operatorname{firstBExitMass}\left(\operatorname{pureLaw}\left(p, q, r, i\right), H, true\right) = 0) \lor (\forall H: \mathbb{N},\ \operatorname{firstBExitMass}\left(\operatorname{pureLaw}\left(p, q, r, i\right), H, false\right) = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.pure_first_B_exit_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A first B from a pure mode enters only one of the two hidden B branches.

**Theorem 1.5 (Empty versus every pure law).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall i: State,\ \frac{1}{5} \leq \operatorname{profileDistance}\left(\operatorname{emptyLaw}\left(p, q, r\right), \operatorname{pureLaw}\left(p, q, r, i\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.empty_pure_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One impossible pure first-B exit category has empty-law mass tending to one fifth along finite horizons.

**Theorem 1.6 (All distinct pure laws are separated).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall i: State,\ (\forall j: State,\ (i \neq j \Rightarrow \operatorname{kappa}\left(p, q, r\right) \leq \operatorname{profileDistance}\left(\operatorname{pureLaw}\left(p, q, r, i\right), \operatorname{pureLaw}\left(p, q, r, j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.pure_pair_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 2-versus-4 pair has complete distance one; every other pair has a positive singleton-coordinate gap.

**Theorem 1.7 (Geometry in both orientations).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall z: \mathbb{R},\ (\forall w: \mathbb{R},\ ((z \in \operatorname{Icc}\left(0, 1\right) \land w \in \operatorname{Icc}\left(0, 1\right)) \Rightarrow (\operatorname{CoherentProfile}\left(\operatorname{orientedMixture}\left(p, q, r, z\right)\right) \land ((\forall H: \mathbb{N},\ \operatorname{TV}\left(\operatorname{at}\left(\operatorname{orientedMixture}\left(p, q, r, z\right), H\right), \operatorname{at}\left(\operatorname{orientedMixture}\left(p, q, r, w\right), H\right)\right) = (\operatorname{abs}\left((z-w)\right)*(1-(\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right))^{H}))) \land \operatorname{profileDistance}\left(\operatorname{orientedMixture}\left(p, q, r, z\right), \operatorname{orientedMixture}\left(p, q, r, w\right)\right) = \operatorname{abs}\left((z-w)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.oriented_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing which branch is dominant changes the mixture coordinate and preserves both metric formulas.

**Theorem 1.8 (Actual startup distances).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall k: \mathbb{N},\ (\forall l: \mathbb{N},\ (\operatorname{CoherentProfile}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right)\right) \land (\operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), \operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((l+1), B\right)\right)\right) = \operatorname{abs}\left((\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), k\right)-\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), l\right))\right) \land \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), \operatorname{dominantLaw}\left(p, q, r\right)\right) = \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), k\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_startup_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every acquired startup has one coherent law, exact pair distance, and exact distance delta_k from the dominant law.

**Theorem 1.9 (The separate half-mixture stratum).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (r = (p+q) \Rightarrow (\forall k: \mathbb{N},\ ((\forall H: \mathbb{N},\ (\forall w: \operatorname{Fin}\left(H\right)\to Visible,\ \operatorname{word}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), H, w\right) = \operatorname{word}\left(\operatorname{mixtureLaw}\left(p, q, r, \frac{1}{2}\right), H, w\right))) \land (\operatorname{CoherentProfile}\left(\operatorname{emptyLaw}\left(p, q, r\right)\right) \land (\operatorname{profileDistance}\left(\operatorname{mixtureLaw}\left(p, q, r, \frac{1}{2}\right), \operatorname{pureLaw}\left(p, q, r, 2\right)\right) = \frac{1}{2} \land \operatorname{profileDistance}\left(\operatorname{mixtureLaw}\left(p, q, r, \frac{1}{2}\right), \operatorname{pureLaw}\left(p, q, r, 4\right)\right) = \frac{1}{2})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.equality_startup_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When r=p+q all finite startup lengths give the half-mixture, whose distances from pure 2 and pure 4 are one half.

**Theorem 1.10 (Unequal startup coordinates are injective).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow \operatorname{Injective}\left(\operatorname{startupCoordinate}\left(p, q, r\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.startup_coordinate_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict minority sequence distinguishes all finite startup indices in either orientation.

**Theorem 1.11 (An interior mixture is a separate law).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall x: \mathbb{R},\ ((0 < x \land x < 1) \Rightarrow ((\forall i: State,\ \operatorname{mixtureLaw}\left(p, q, r, x\right) \neq \operatorname{pureLaw}\left(p, q, r, i\right)) \land \operatorname{mixtureLaw}\left(p, q, r, x\right) \neq \operatorname{emptyLaw}\left(p, q, r\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.interior_mixture_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both branch coordinates remain positive, so no interior mixture is a pure or empty law.

**Theorem 1.12 (Distinct actual startup lengths).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow \operatorname{Injective}\left(\operatorname{actualStartupLaw}\left(p, q, r\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_startup_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

actualStartupLaw k is actualFutureWordWeight after the acquired word B^(k+1).

**Theorem 1.13 (Actual predictive-law class distinctness).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{Injective}\left(\operatorname{pureLaw}\left(p, q, r\right)\right) \land ((\forall i: State,\ \operatorname{emptyLaw}\left(p, q, r\right) \neq \operatorname{pureLaw}\left(p, q, r, i\right)) \land (\forall k: \mathbb{N},\ ((\forall i: State,\ \operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right) \neq \operatorname{pureLaw}\left(p, q, r, i\right)) \land \operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right) \neq \operatorname{emptyLaw}\left(p, q, r\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_predictive_class_distinctness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All five pure laws differ; the empty law is additional; every finite startup law is interior and differs from them.

**Theorem 1.14 (Cutoff and decay in the actual metric).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (0 < \operatorname{N2}\left(p, q, r, epsilon\right) \land (\operatorname{N2}\left(p, q, r, epsilon\right) = \operatorname{ceilNat}\left(\frac{\operatorname{log}\left(\frac{(1-(2*epsilon))}{(2*epsilon)}\right)}{\operatorname{abs}\left(\operatorname{log}\left(\operatorname{theta}\left(p, q, r\right)\right)\right)}\right) \land ((\forall k: \mathbb{N},\ (\operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), \operatorname{dominantLaw}\left(p, q, r\right)\right) \leq (2*epsilon) \iff \operatorname{N2}\left(p, q, r, epsilon\right) \leq k)) \land ((\forall i: \mathbb{N},\ (i < \operatorname{N2}\left(p, q, r, epsilon\right) \Rightarrow (2*epsilon) < \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((i+1), B\right)\right), \operatorname{dominantLaw}\left(p, q, r\right)\right))) \land ((\operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((\operatorname{N2}\left(p, q, r, epsilon\right)+1), B\right)\right), \operatorname{dominantLaw}\left(p, q, r\right)\right) = (2*epsilon) \iff \frac{\operatorname{log}\left(\frac{(1-(2*epsilon))}{(2*epsilon)}\right)}{\operatorname{abs}\left(\operatorname{log}\left(\operatorname{theta}\left(p, q, r\right)\right)\right)} = \operatorname{castReal}\left(\operatorname{N2}\left(p, q, r, epsilon\right)\right)) \land \operatorname{Tendsto}\left(\operatorname{actualStartupDistance}\left(p, q, r\right), atTop, \operatorname{nhds}\left(0\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_cutoff_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

N2 is the first non-strict actual distance threshold. The formula, earlier strict inequalities, exact ties and decay are simultaneous.

**Theorem 1.15 (One coherent midpoint bounds the tail).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (\operatorname{CoherentProfile}\left(\operatorname{orientedMixture}\left(p, q, r, \frac{\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, epsilon\right)\right)}{2}\right)\right) \land (\operatorname{profileDistance}\left(\operatorname{dominantLaw}\left(p, q, r\right), \operatorname{orientedMixture}\left(p, q, r, \frac{\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, epsilon\right)\right)}{2}\right)\right) \leq epsilon \land (\forall k: \mathbb{N},\ (\operatorname{N2}\left(p, q, r, epsilon\right) \leq k \Rightarrow \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), \operatorname{orientedMixture}\left(p, q, r, \frac{\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, epsilon\right)\right)}{2}\right)\right) \leq epsilon)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.startup_midpoint_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The midpoint beta=delta_N2/2 is within epsilon of the dominant law and every actual startup law with k>=N2.

**Theorem 1.16 (Classes under a length cap).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall L: \mathbb{N},\ (2 \leq L \Rightarrow (\operatorname{Injective}\left(\operatorname{cappedClassLaw}\left(p, q, r, L\right)\right) \land ((\forall t: \operatorname{Sum}\left(State, \operatorname{Fin}\left(L\right)\right),\ (\exists h: \operatorname{List}\left(Visible\right),\ ((h \neq \operatorname{nil}\left(\right) \land \operatorname{length}\left(h\right) \leq L) \land (0 < \operatorname{historyMass}\left(p, q, r, h\right) \land \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{apply}\left(\operatorname{cappedClassLaw}\left(p, q, r, L\right), t\right))))) \land ((\forall h: \operatorname{List}\left(Visible\right),\ (((h \neq \operatorname{nil}\left(\right) \land \operatorname{length}\left(h\right) \leq L) \land 0 < \operatorname{historyMass}\left(p, q, r, h\right)) \Rightarrow (\exists t: \operatorname{Sum}\left(State, \operatorname{Fin}\left(L\right)\right),\ \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{apply}\left(\operatorname{cappedClassLaw}\left(p, q, r, L\right), t\right)))) \land \operatorname{card}\left(\operatorname{Sum}\left(State, \operatorname{Fin}\left(L\right)\right)\right) = (L+5)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.capped_predictive_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For L>=2 and a!=b there are L+5 realized post-read law classes, with both realization and exhaustive coverage.

**Theorem 1.17 (Classes at one fixed length).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall L: \mathbb{N},\ (2 \leq L \Rightarrow (\operatorname{Injective}\left(\operatorname{fixedClassLaw}\left(p, q, r, L\right)\right) \land ((\forall t: \operatorname{Sum}\left(State, Unit\right),\ (\exists h: \operatorname{List}\left(Visible\right),\ (\operatorname{length}\left(h\right) = L \land (0 < \operatorname{historyMass}\left(p, q, r, h\right) \land \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{apply}\left(\operatorname{fixedClassLaw}\left(p, q, r, L\right), t\right))))) \land ((\forall h: \operatorname{List}\left(Visible\right),\ ((\operatorname{length}\left(h\right) = L \land 0 < \operatorname{historyMass}\left(p, q, r, h\right)) \Rightarrow (\exists t: \operatorname{Sum}\left(State, Unit\right),\ \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{apply}\left(\operatorname{fixedClassLaw}\left(p, q, r, L\right), t\right)))) \land \operatorname{card}\left(\operatorname{Sum}\left(State, Unit\right)\right) = 6)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.fixed_length_predictive_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible triple and L>=2 the single fixed-length history domain has six realized law classes.

**Theorem 1.18 (The capped empty boundary adds one class).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall L: \mathbb{N},\ (2 \leq L \Rightarrow (\operatorname{Injective}\left(\operatorname{OptionCase}\left(\operatorname{emptyLaw}\left(p, q, r\right), \operatorname{cappedClassLaw}\left(p, q, r, L\right)\right)\right) \land \operatorname{card}\left(\operatorname{Option}\left(\operatorname{Sum}\left(State, \operatorname{Fin}\left(L\right)\right)\right)\right) = (L+6)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.initialized_capped_class_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initialized capped family has L+6 distinct laws. This count includes the queryable empty boundary.

**Theorem 1.19 (Equality has six or seven law classes).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (r = (p+q) \Rightarrow (\operatorname{Injective}\left(\operatorname{fixedClassLaw}\left(p, q, r, 2\right)\right) \land ((\forall t: \operatorname{Sum}\left(State, Unit\right),\ (\exists h: \operatorname{List}\left(Visible\right),\ (h \neq \operatorname{nil}\left(\right) \land (0 < \operatorname{historyMass}\left(p, q, r, h\right) \land \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{apply}\left(\operatorname{fixedClassLaw}\left(p, q, r, 2\right), t\right))))) \land ((\forall h: \operatorname{List}\left(Visible\right),\ ((h \neq \operatorname{nil}\left(\right) \land 0 < \operatorname{historyMass}\left(p, q, r, h\right)) \Rightarrow (\exists t: \operatorname{Sum}\left(State, Unit\right),\ \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{apply}\left(\operatorname{fixedClassLaw}\left(p, q, r, 2\right), t\right)))) \land (\operatorname{Injective}\left(\operatorname{OptionCase}\left(\operatorname{emptyLaw}\left(p, q, r\right), \operatorname{fixedClassLaw}\left(p, q, r, 2\right)\right)\right) \land (\operatorname{card}\left(\operatorname{Sum}\left(State, Unit\right)\right) = 6 \land \operatorname{card}\left(\operatorname{Option}\left(\operatorname{Sum}\left(State, Unit\right)\right)\right) = 7))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.equality_predictive_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-length equality domain has six post-read laws and an additional initialized empty law, with actual realization and coverage.

**Theorem 1.20 (Every pre-cutoff startup class is separate).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (\forall k: \mathbb{N},\ (k < \operatorname{N2}\left(p, q, r, epsilon\right) \Rightarrow ((\forall j: State,\ (2*epsilon) < \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), \operatorname{pureLaw}\left(p, q, r, j\right)\right)) \land (2*epsilon) < \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{replicate}\left((k+1), B\right)\right), \operatorname{emptyLaw}\left(p, q, r\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.startup_transient_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every index strictly below N2 is more than 2 epsilon from each pure law and from the empty law.

**Theorem 1.21 (Countably infinite exact images).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\operatorname{CountableSet}\left(\operatorname{postreadLawSet}\left(p, q, r\right)\right) \land (\operatorname{Infinite}\left(\operatorname{postreadLawSet}\left(p, q, r\right)\right) \land (\operatorname{CountableSet}\left(\operatorname{initializedLawSet}\left(p, q, r\right)\right) \land \operatorname{Infinite}\left(\operatorname{initializedLawSet}\left(p, q, r\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.unequal_exact_classes_countably_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All finite actual histories form a countable domain, while the positive all-B startup orbit supplies an injection from the naturals.

**Theorem 1.22 (Actual five-mode predictive geometry).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow \operatorname{PredictiveGeometry}\left(p, q, r\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.five_mode_predictive_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PredictiveGeometry collects the exact branch support and holding masses, finite and complete mixture geometry, coherence, positive kappa, pure, singleton, mixture and empty separations, finite empty exit masses, actual startup laws, exact cutoff, the coherent midpoint tail bound, fixed and capped class injections, equality classes and the unequal countably infinite images. Its only premise is source admissibility.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_cutoff_geometry`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_predictive_class_distinctness`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_startup_geometry`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.actual_startup_injective`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.branch_exit_masses`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.capped_predictive_classes`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.coherent_mixture_geometry`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.empty_first_B_exit_masses`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.empty_pure_separation`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.equality_predictive_classes`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.equality_startup_geometry`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.five_mode_predictive_geometry`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.fixed_length_predictive_classes`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.initialized_capped_class_count`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.interior_mixture_distinct`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.oriented_geometry`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.pure_first_B_exit_zero`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.pure_pair_separation`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.startup_coordinate_injective`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.startup_midpoint_tail_bound`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.startup_transient_separation`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry.unequal_exact_classes_countably_infinite`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core](FiveModePredictiveLawGeometry/Core.md)
