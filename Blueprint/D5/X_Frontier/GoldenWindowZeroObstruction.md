# Golden Window Zero Obstruction

## Abstract

Normal-form candidates are obstructed, while bare meromorphic candidates evade point tests.

**Definition 1.1 (O-5 window localization).**

$$O5WindowLocalization = \left(\exists Zqc \in \mathbb{C} \to \mathbb{C},\; \operatorname{MeromorphicOn}\left(Zqc, \left\{0 < \Re{s} \mid s \in \mathbb{C}\right\}\right) \land \left(\left(\forall s \in \mathbb{C},\; \frac{1}{\varphi^{2}} < \Re{s} \Rightarrow Zqc\left(s\right) = eulerGerm\left(s\right)\right) \land \left(\forall s \in \mathbb{C},\; \frac{1}{2 \cdot \varphi^{3}} < \Re{s} \Rightarrow \left(\Re{s} < \frac{1}{\varphi^{2}} \Rightarrow \left(\operatorname{AnalyticAt}\left(\mathbb{C}, Zqc, s\right) \Rightarrow \left(Zqc\left(s\right) = 0 \Rightarrow \Re{s} = structuralZero\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/X_Frontier/GoldenWindowZeroObstruction.O5WindowLocalization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition restates the O-5 localization proposition directly. It asks for a meromorphic right-half-plane continuation that agrees with eulerGerm to the right of the golden window and places every analytic zero inside the open window on structuralZero.

The definition uses phi, eulerGerm, and structuralZero from Hearts, but it does not depend on the open proof of o5_independence.

**Theorem 1.2 (An off-line analytic zero obstructs normal-form candidates).**

$$\forall W \in \mathbb{C} \to \mathbb{C}, s0 \in \mathbb{C}, r \in \mathbb{R},\; 0 < r \Rightarrow \left(r < \frac{1}{\varphi^{2}} \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, W, \left\{r < \Re{s} \mid s \in \mathbb{C}\right\}\right) \Rightarrow \left(\left(\forall s \in \mathbb{C},\; \frac{1}{\varphi^{2}} < \Re{s} \Rightarrow W\left(s\right) = eulerGerm\left(s\right)\right) \Rightarrow \left(\frac{1}{2 \cdot \varphi^{3}} < \Re{s0} \Rightarrow \left(\Re{s0} < \frac{1}{\varphi^{2}} \Rightarrow \left(r < \Re{s0} \Rightarrow \left(W\left(s0\right) = 0 \Rightarrow \left(\Re{s0} \ne structuralZero \Rightarrow \left(\neg \left(\exists Zqc \in \mathbb{C} \to \mathbb{C},\; \operatorname{MeromorphicOn}\left(Zqc, \left\{0 < \Re{s} \mid s \in \mathbb{C}\right\}\right) \land \left(\left(\forall s \in \mathbb{C},\; \frac{1}{\varphi^{2}} < \Re{s} \Rightarrow Zqc\left(s\right) = eulerGerm\left(s\right)\right) \land \left(\operatorname{MeromorphicNFOn}\left(Zqc, \left\{r < \Re{s} \mid s \in \mathbb{C}\right\}\right) \land \left(\forall s \in \mathbb{C},\; \frac{1}{2 \cdot \varphi^{3}} < \Re{s} \Rightarrow \left(\Re{s} < \frac{1}{\varphi^{2}} \Rightarrow \left(\operatorname{AnalyticAt}\left(\mathbb{C}, Zqc, s\right) \Rightarrow \left(Zqc\left(s\right) = 0 \Rightarrow \Re{s} = structuralZero\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/X_Frontier/GoldenWindowZeroObstruction.no_normal_form_o5_candidate_of_offline_analytic_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be analytic on the half-plane Re(s) greater than r and agree with eulerGerm to the right of the golden window. If W has a zero inside the window whose real part differs from structuralZero, then no candidate satisfying the displayed MeromorphicNFOn contract can pass the guarded zero test.

The regularity requirement belongs to each candidate inside the negated existential. There is no external premise asserting that every bare meromorphic representative is in normal form.

The proof applies the repository theorem meromorphic_continuation_unique on the connected half-plane. Equality on the nonempty open right sub-half-plane is derived from the two eulerGerm agreement clauses, and equality at the proposed zero is therefore a conclusion rather than an added hypothesis.

This theorem does not refute O5WindowLocalization or claim that O-5 is false. The frozen O-5 statement allows arbitrary meromorphic representatives, so a genuine refutation would first require a stronger candidate contract. The required zero also remains conditional: issue #5032 supplies numerical evidence, not a formal existence proof.

**Theorem 1.3 (A bare meromorphic candidate evades a guarded point test).**

$$\forall W \in \mathbb{C} \to \mathbb{C}, x \in \mathbb{C}, r \in \mathbb{R},\; r < \Re{x} \Rightarrow \left(\Re{x} < \frac{1}{\varphi^{2}} \Rightarrow \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, W, \left\{r < \Re{s} \mid s \in \mathbb{C}\right\}\right) \Rightarrow \left(\left(\forall s \in \mathbb{C},\; \frac{1}{\varphi^{2}} < \Re{s} \Rightarrow W\left(s\right) = eulerGerm\left(s\right)\right) \Rightarrow \left(\exists Zqc \in \mathbb{C} \to \mathbb{C},\; \operatorname{MeromorphicOn}\left(Zqc, \left\{r < \Re{s} \mid s \in \mathbb{C}\right\}\right) \land \left(\left(\forall s \in \mathbb{C},\; \frac{1}{\varphi^{2}} < \Re{s} \Rightarrow Zqc\left(s\right) = eulerGerm\left(s\right)\right) \land \left(\neg \operatorname{AnalyticAt}\left(\mathbb{C}, Zqc, x\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/X_Frontier/GoldenWindowZeroObstruction.bare_meromorphic_candidate_evades_zero_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be analytic on Re(s) greater than r and agree with eulerGerm to the right of the golden window. At any point x in that analytic half-plane but left of the agreement region, changing only W(x) produces a candidate that remains meromorphic and preserves the agreement clause, but is not analytic at x.

The witness is Function.update W x (W x + 1). Mathlib's MeromorphicAt.update proves that the single-point change preserves meromorphy, while continuousAt_update_same and uniqueness of limits show that analyticity at x would force one to equal zero.

This positive result formalizes the limitation in the original O-5 statement: its AnalyticAt guard can be made false at a selected point without violating bare MeromorphicOn. Therefore the normal-form obstruction above is not a refutation of frozen O-5.

## References

- Truth anchor: `D5/X_Frontier/GoldenWindowZeroObstruction.O5WindowLocalization`
- Truth anchor: `D5/X_Frontier/GoldenWindowZeroObstruction.bare_meromorphic_candidate_evades_zero_test`
- Truth anchor: `D5/X_Frontier/GoldenWindowZeroObstruction.no_normal_form_o5_candidate_of_offline_analytic_zero`
- Dependency: [D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness](../S3/Analytic/Isolation/MeromorphicContinuationUniqueness.md)
