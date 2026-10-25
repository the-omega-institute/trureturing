# Complete signed-ball analytic reduction

## Abstract

From a copy in the full signed dual ball to a normalized disjoint sequence, and from signed clopen collision to nonembedding.

**Theorem 1.1 (KPR normalization and full-domain thinning).**

$$\forall K: Type, [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{T2Space}\left(K\right)] [\operatorname{MeasurableSpace}\left(K\right)] [\operatorname{BorelSpace}\left(K\right)] \forall h: \operatorname{StoneCech}\left(Nat\right) \to \operatorname{WeakDual}\left(Real, \operatorname{ContinuousMap}\left(K, Real\right)\right), {\operatorname{Continuous}\left(h\right) \land \operatorname{Injective}\left(h\right) \land \forall p: \operatorname{StoneCech}\left(Nat\right), \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{h}\left(p\right)\right)\right) \le 1} \Rightarrow {\exists b: Nat \to \operatorname{SignedMeasure}\left(K\right), \exists E: Nat \to \operatorname{Set}\left(K\right), \exists f: \operatorname{Ultrafilter}\left(Nat\right) \to \operatorname{WeakDual}\left(Real, \operatorname{ContinuousMap}\left(K, Real\right)\right), \forall n: Nat, \operatorname{Regular}\left(\operatorname{totalVariation}\left(\operatorname{b}\left(n\right)\right)\right) \land \forall n: Nat, \operatorname{real}\left(\operatorname{totalVariation}\left(\operatorname{b}\left(n\right)\right), univ\right) = 1 \land \forall n: Nat, \operatorname{MeasurableSet}\left(\operatorname{E}\left(n\right)\right) \land \operatorname{PairwiseDisjoint}\left(E\right) \land \forall n: Nat, \operatorname{apply}\left(\operatorname{totalVariation}\left(\operatorname{b}\left(n\right)\right), \operatorname{compl}\left(\operatorname{E}\left(n\right)\right)\right) = 0 \land \operatorname{Continuous}\left(f\right) \land \operatorname{Injective}\left(f\right) \land \forall n: Nat, \operatorname{f}\left(\operatorname{pure}\left(n\right)\right) = \operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(\operatorname{b}\left(n\right)\right)\right) \land \forall p: \operatorname{Ultrafilter}\left(Nat\right), \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{f}\left(p\right)\right)\right) \le 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedBallReduction.exists_normalized_disjoint_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is any compact Hausdorff Borel space, without a metrizability or zero-dimensionality hypothesis. h is an arbitrary weak-star continuous injection of StoneCech Nat into the entire real signed dual unit ball of C(K,Real). The output consists of actual regular signed measures b(n), pairwise disjoint Borel sets E(n) carrying their total variations, and a continuous injective extension f on every ultrafilter. Each b(n) has variation mass one, f(pure n) is its integration functional, and every f(p) has strong-dual norm at most one.

Signed Riesz represents the original principal functionals by regular signed measures. The actual raw signed KPR theorem selects literal restrictions u(n) and v(n), with u(n) carried by disjoint Borel sets, v(n) converging against every continuous linear functional on the dual, and norm(u(n)) tending to a nonnegative real r. The selected original extension remains injective because mapping ultrafilters along an injection is injective.

At every free ultrafilter, the v extension equals its one weak limit V. Consequently the u extension is the selected original extension minus V. If r were zero, u would tend to zero in norm and the original extension would be constant on the free part. Two distinct free ultrafilters contradict its injection. Thus r is positive, and a tail has strictly positive actual norms.

Define b(n)=u(n)/norm(u(n)) on this tail. The regularity, unit norm and literal carrying set follow from scalar total variation and restriction identities. normalize_sub_tendsto_zero controls the norm difference between this sequence and u(n)/r. It vanishes on every free ultrafilter, so the free extension is the selected original extension minus V, divided by r. This proves free/free injection. Disjoint carriers and mass one prove principal/principal injection. CountableAvoidance removes every principal/free collision by an actual increasing subsequence, leaving a full injective extension.

**Definition 1.2 (The analytic collision premise).**

$$\forall K: Type, [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{T2Space}\left(K\right)] [\operatorname{MeasurableSpace}\left(K\right)] [\operatorname{BorelSpace}\left(K\right)] \operatorname{SignedClopenCollision}\left(K\right) = \forall s: Nat \to \operatorname{SignedMeasure}\left(K\right), \forall W: Nat \to \operatorname{Set}\left(K\right), {\forall n: Nat, \operatorname{Regular}\left(\operatorname{totalVariation}\left(\operatorname{s}\left(n\right)\right)\right) \land \forall n: Nat, \operatorname{real}\left(\operatorname{totalVariation}\left(\operatorname{s}\left(n\right)\right), univ\right) = 1 \land \forall n: Nat, \operatorname{IsClopen}\left(\operatorname{W}\left(n\right)\right) \land \operatorname{Nonempty}\left(\operatorname{W}\left(n\right)\right) \land \operatorname{PairwiseDisjoint}\left(W\right) \land \forall n: Nat, \operatorname{apply}\left(\operatorname{totalVariation}\left(\operatorname{s}\left(n\right)\right), \operatorname{compl}\left(\operatorname{W}\left(n\right)\right)\right) = 0 \land \forall n: Nat, \frac{1}{2} \le \operatorname{real}\left(\operatorname{posPart}\left(\operatorname{toJordanDecomposition}\left(\operatorname{s}\left(n\right)\right)\right), univ\right)} \Rightarrow {\forall f: \operatorname{Ultrafilter}\left(Nat\right) \to \operatorname{WeakDual}\left(Real, \operatorname{ContinuousMap}\left(K, Real\right)\right), {\operatorname{Continuous}\left(f\right) \land \forall n: Nat, \operatorname{f}\left(\operatorname{pure}\left(n\right)\right) = \operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(\operatorname{s}\left(n\right)\right)\right)} \Rightarrow {\exists p: \operatorname{Ultrafilter}\left(Nat\right), \exists q: \operatorname{Ultrafilter}\left(Nat\right), \operatorname{toFilter}\left(p\right) \le cofinite \land \operatorname{toFilter}\left(q\right) \le cofinite \land p \neq q \land \operatorname{f}\left(p\right) = \operatorname{f}\left(q\right)}}$$

*Formalization.* `D5/S3/Topology/Measures/SignedBallReduction.SignedClopenCollision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate quantifies over every natural-number sequence of regular signed measures of variation mass one and every pairwise disjoint sequence of nonempty clopens carrying them. It requires positive Jordan-part mass at least one half for every term. For every weak-star continuous extension of the exact principal integration functionals, it gives two distinct free ultrafilters with equal images. It does not assume nonembedding or any KPR, normalization, approximation or extension supplier.

**Theorem 1.3 (Exclusion of the entire signed unit ball).**

$$\forall K: Type, [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{T2Space}\left(K\right)] [\operatorname{MeasurableSpace}\left(K\right)] [\operatorname{BorelSpace}\left(K\right)] [\operatorname{ZeroDimensionalSpace}\left(K\right)] \forall h: \operatorname{StoneCech}\left(Nat\right) \to \operatorname{WeakDual}\left(Real, \operatorname{ContinuousMap}\left(K, Real\right)\right), {\operatorname{SignedClopenCollision}\left(K\right) \land \operatorname{Continuous}\left(h\right) \land \forall p: \operatorname{StoneCech}\left(Nat\right), \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{h}\left(p\right)\right)\right) \le 1} \Rightarrow {\neg \operatorname{Injective}\left(h\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedBallReduction.not_injective_signed_ball_of_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume K is also zero-dimensional and satisfies SignedClopenCollision. A supposed signed-ball embedding yields the normalized disjoint-Borel sequence above. The existing WeakStarNormSeparation theorem gives one c greater than zero for all unequal points of its entire extension. Choose eta=min(c/16,1/4).

The actual exists_signed_clopen_disjointization theorem supplies increasing selections, disjoint nonempty clopens, normalized regular signed restrictions, and a single sign s in {1,-1} after another increasing selection. The entire selected original sequence and the approximants are multiplied by that same sign. Each approximant has positive Jordan mass at least one half, and its variation distance from the corresponding signed original term is less than twice eta.

Reindexing and the fixed sign retain the full norm gap c. Banach–Alaoglu supplies the approximant extension. Weak-star closed norm balls transfer the twice-eta bound from every principal point to every ultrafilter. Since four eta is less than c, injective_of_approximation makes that full extension injective. SignedClopenCollision gives two distinct free points with the same value, a contradiction. The collision premise must still be established for the intended CH construction; this analytic reduction does not realize the transfinite construction or assert that the full CH target is solved.

## References

- Truth anchor: `D5/S3/Topology/Measures/SignedBallReduction.SignedClopenCollision`
- Truth anchor: `D5/S3/Topology/Measures/SignedBallReduction.exists_normalized_disjoint_embedding`
- Truth anchor: `D5/S3/Topology/Measures/SignedBallReduction.not_injective_signed_ball_of_collision`
- Dependency: [D5/S3/Topology/Measures/ClopenDisjointization](ClopenDisjointization.md)
- Dependency: [D5/S3/Topology/Measures/SignedGrothendieckCriterion](SignedGrothendieckCriterion.md)
- Dependency: [D5/S3/Topology/Measures/WeakStarPerturbation](WeakStarPerturbation.md)
- Dependency: [D5/S3/Topology/StoneCech/CountableAvoidance](../StoneCech/CountableAvoidance.md)
