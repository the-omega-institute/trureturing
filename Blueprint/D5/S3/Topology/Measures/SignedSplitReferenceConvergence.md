# Signed reference convergence on the actual closed split

## Abstract

A fixed signed reference and increasing-set side errors give actual represented whole-sequence convergence on a closed Boolean split.

K is any compact metric totally disconnected Borel space. Y and Z are closed; neither coverage nor nonemptiness is assumed. Split is exactly the subtype of K × Bool consisting of (Y,false) and (Z,true), with first-coordinate projection π and clopen sheets S_false and S_true.

**Theorem 1.1 (Represented signed split limit).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \operatorname{CompactMetricTotallyDisconnectedBorel}\left(K\right)\\\forall Y: \operatorname{Set}\left(K\right), \forall Z: \operatorname{Set}\left(K\right), \operatorname{IsClosed}\left(Y\right) \land \operatorname{IsClosed}\left(Z\right) \Rightarrow\\L = {p:\operatorname{Product}\left(K, \operatorname{Bool}\left(\right)\right) suchThat {\operatorname{mem}\left(\operatorname{fst}\left(p\right), Y\right) \land \operatorname{snd}\left(p\right) = \operatorname{false}\left(\right)} \lor {\operatorname{mem}\left(\operatorname{fst}\left(p\right), Z\right) \land \operatorname{snd}\left(p\right) = \operatorname{true}\left(\right)}}\\\forall C: \operatorname{Real}\left(\right), \forall s: \operatorname{Nat}\left(\right) \to \operatorname{SignedMeasure}\left(L\right), \\\operatorname{Nonneg}\left(C\right) \land {\forall n: \operatorname{Nat}\left(\right), \operatorname{totalVariationRealUniv}\left(\operatorname{s}\left(n\right)\right) \le C} \Rightarrow\\\forall mu: \operatorname{SignedMeasure}\left(K\right), \forall U: \operatorname{Nat}\left(\right) \to \operatorname{Set}\left(K\right), \\{\forall n: \operatorname{Nat}\left(\right), \operatorname{MeasurableSet}\left(\operatorname{U}\left(n\right)\right)} \land \operatorname{Monotone}\left(U\right) \Rightarrow\\\forall epsilon: \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), \operatorname{Tendsto}\left(epsilon, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right) \Rightarrow\\{\forall A: \operatorname{Set}\left(K\right), \operatorname{IsClopen}\left(A\right) \Rightarrow \operatorname{Tendsto}\left(n \mapsto \operatorname{apply}\left(\operatorname{map}\left(\operatorname{s}\left(n\right), projection\right), A\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{mu}\left(A\right)\right)\right)} \Rightarrow\\{\forall A: \operatorname{Set}\left(K\right), \operatorname{IsClopen}\left(A\right) \Rightarrow \operatorname{Eventually}\left(\operatorname{atTop}\left(\right), n \mapsto \operatorname{abs}\left(\operatorname{apply}\left(\operatorname{s}\left(n\right), \operatorname{inter}\left(\operatorname{side}\left(\operatorname{true}\left(\right)\right), \operatorname{preimage}\left(projection, A\right)\right)\right) - \operatorname{mu}\left(\operatorname{inter}\left(A, \operatorname{U}\left(n\right)\right)\right)\right) \le \operatorname{epsilon}\left(n\right)\right)} \Rightarrow\\\exists nu:\operatorname{SignedMeasure}\left(L\right), \operatorname{totalVariationRealUniv}\left(nu\right) \le C \land \operatorname{Regular}\left(\operatorname{jordanPosPart}\left(nu\right)\right) \land \operatorname{Regular}\left(\operatorname{jordanNegPart}\left(nu\right)\right) \land \operatorname{Tendsto}\left(n \mapsto \operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(\operatorname{s}\left(n\right)\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{toWeakDual}\left(\operatorname{signedFunctional}\left(nu\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedSplitReferenceConvergence.exists_signed_limit_of_reference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sequence s consists of arbitrary actual SignedMeasure values on Split with totalVariation.real(univ) ≤ C and C ≥ 0. One fixed signed μ on K is used for every test and every stage. The measurable U_n increase, and ε_n tends to zero. For each fixed ambient clopen A, projected s_n(A) tends to μ(A), and eventually the absolute true-sheet error against μ(A ∩ U_n) is at most ε_n. No global nonnegativity of ε is required.

For a clopen W of Split, the projected images of W ∩ S_e and Wᶜ ∩ S_e are disjoint compact closed sets. Projection is injective within each fixed tag. The existing compact zero-dimensional clopen separator supplies an ambient clopen B_e with W ∩ S_e = S_e ∩ π⁻¹(B_e); it does not assert that the projected traces themselves are ambient clopens.

Signed continuity from below gives μ(A ∩ U_n) → μ(A ∩ ⋃ U_n). The vanishing absolute-error bound gives this same limit for s_n(S_true ∩ π⁻¹(A)). Disjoint finite additivity proves s_n(W) = (π_*s_n)(B_false) − s_n(S_true ∩ π⁻¹(B_false)) + s_n(S_true ∩ π⁻¹(B_true)). Thus every clopen coordinate converges, hence is Cauchy. The live ClopenCauchyConvergence helper then yields an actual signed ν, the same variation upper bound, regular Jordan parts, and weak-star convergence of the entire represented sequence.

Empty K and Split, C = 0, negative coefficients, and mixed signs are included. The conclusion is a variation bound, not variation-mass convergence or exact norm preservation. This bridge is an internal reference-convergence step for F in exists_signed_split_successor. It does not supply the CH construction, every-choice convergence, an anti-homeomorphism, either remaining analytic endpoint, or a complete solution of Talagrand Problem 8.2. FullCHLeanSolved = 0 and officialSolved = 0.

## References

- Truth anchor: `D5/S3/Topology/Measures/SignedSplitReferenceConvergence.exists_signed_limit_of_reference`
- Dependency: [D5/S3/Topology/Measures/ClopenCauchyConvergence](ClopenCauchyConvergence.md)
