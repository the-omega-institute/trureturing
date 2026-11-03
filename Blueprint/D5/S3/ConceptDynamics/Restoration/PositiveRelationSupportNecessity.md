# Positive Relation Support Necessity

## Abstract

Unrestricted full injections and unused ambient labels force positive certificates to expose every nonisolated endpoint on both sides.

**Definition 1.1 (Transport by full injections).**

$$\forall A: Type, \forall B: Type, \forall L: Type, \forall R: Type, \forall E: \operatorname{SetRel}\left(A, B\right), \forall l: \operatorname{Embedding}\left(A, L\right), \forall r: \operatorname{Embedding}\left(B, R\right), \operatorname{transport}\left(E, l, r\right) = \operatorname{image}\left(\operatorname{ProdMap}\left(l, r\right), E\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embedding denotes a full injective function, SetRel a set of ordered pairs, and image and ProdMap have their usual set and product meanings. The transported target contains the entire source relation.

**Theorem 1.2 (An unexposed left label admits a competing full injection).**

$$\forall A: Type, \forall B: Type, \forall L: Type, \forall R: Type, \forall E: \operatorname{SetRel}\left(A, B\right), \forall l: \operatorname{Embedding}\left(A, L\right), \forall r: \operatorname{Embedding}\left(B, R\right), \forall D: \operatorname{SetRel}\left(L, R\right), \forall a: A, \forall c: L, ((D \subseteq \operatorname{transport}\left(E, l, r\right)) \land\\{}(\exists b: B, (a, b) \in E) \land\\{}(\neg l(a) \in \operatorname{dom}\left(D\right)) \land\\{}(\neg c \in \operatorname{range}\left(l\right))) \Rightarrow\\{}\exists f: \operatorname{Embedding}\left(A, L\right), (f(a) = c) \land\\{}(\forall x: A, (x \neq a) \Rightarrow\\{}f(x) = l(x)) \land\\{}(D \subseteq \operatorname{transport}\left(E, f, r\right)) \land\\{}(\operatorname{transport}\left(E, f, r\right) \neq \operatorname{transport}\left(E, l, r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.unexposed_left_label_competitor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compose the full left embedding with the ambient transposition exchanging its selected label and the unused label. Injectivity follows from composition with an equivalence. Every evidence edge avoids the selected endpoint, so its two labels stay fixed. An incident edge now uses the fresh label, which no old edge uses. No finiteness assumption is needed for this construction.

**Theorem 1.3 (An unexposed right label admits a competing full injection).**

$$\forall A: Type, \forall B: Type, \forall L: Type, \forall R: Type, \forall E: \operatorname{SetRel}\left(A, B\right), \forall l: \operatorname{Embedding}\left(A, L\right), \forall r: \operatorname{Embedding}\left(B, R\right), \forall D: \operatorname{SetRel}\left(L, R\right), \forall b: B, \forall c: R, ((D \subseteq \operatorname{transport}\left(E, l, r\right)) \land\\{}(\exists a: A, (a, b) \in E) \land\\{}(\neg r(b) \in \operatorname{cod}\left(D\right)) \land\\{}(\neg c \in \operatorname{range}\left(r\right))) \Rightarrow\\{}\exists f: \operatorname{Embedding}\left(B, R\right), (f(b) = c) \land\\{}(\forall x: B, (x \neq b) \Rightarrow\\{}f(x) = r(x)) \land\\{}(D \subseteq \operatorname{transport}\left(E, l, f\right)) \land\\{}(\operatorname{transport}\left(E, l, f\right) \neq \operatorname{transport}\left(E, l, r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.unexposed_right_label_competitor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right embedding is composed with its ambient transposition. The same source relation and the original left embedding remain in the competitor. Its fresh right label witnesses a genuinely different transported target while all acquired positive pairs survive.

**Theorem 1.4 (Target-constant positive evidence exposes both supports).**

$$\forall A: Type, \forall B: Type, \forall L: Type, \forall R: Type, [\operatorname{Fintype}\left(A\right)], [\operatorname{Fintype}\left(B\right)], [\operatorname{Fintype}\left(L\right)], [\operatorname{Fintype}\left(R\right)], [\operatorname{DecidableEq}\left(L\right)], [\operatorname{DecidableEq}\left(R\right)],\\{}\forall E: \operatorname{SetRel}\left(A, B\right), \forall l: \operatorname{Embedding}\left(A, L\right), \forall r: \operatorname{Embedding}\left(B, R\right), \forall D: \operatorname{Finset}\left(L \times R\right), ((D \subseteq \operatorname{transport}\left(E, l, r\right)) \land\\{}(\forall a: A, \exists b: B, (a, b) \in E) \land\\{}(\forall b: B, \exists a: A, (a, b) \in E) \land\\{}(\operatorname{card}\left(A\right) < \operatorname{card}\left(L\right)) \land\\{}(\operatorname{card}\left(B\right) < \operatorname{card}\left(R\right)) \land\\{}(\forall f: \operatorname{Embedding}\left(A, L\right), \forall g: \operatorname{Embedding}\left(B, R\right), (D \subseteq \operatorname{transport}\left(E, f, g\right)) \Rightarrow\\{}\operatorname{transport}\left(E, f, g\right) = \operatorname{transport}\left(E, l, r\right))) \Rightarrow\\{}(\operatorname{dom}\left(D\right) = \operatorname{range}\left(l\right)) \land\\{}(\operatorname{cod}\left(D\right) = \operatorname{range}\left(r\right)) \land\\{}(\operatorname{max}\left(\operatorname{card}\left(A\right), \operatorname{card}\left(B\right)\right) \leq \operatorname{card}\left(D\right)) \land\\{}(\forall s: \operatorname{List}\left(L \times R\right), (\operatorname{toFinset}\left(s\right) = D) \Rightarrow\\{}\operatorname{max}\left(\operatorname{card}\left(A\right), \operatorname{card}\left(B\right)\right) \leq \operatorname{length}\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.positive_certificate_support_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The version domain contains every pair of full embeddings of this same source. Attainment supplies the original pair, and constancy is required over every compatible pair. Ambient cardinal slack produces an unused label on each side. If a used label were missing, the corresponding competitor would contradict constancy.

The domain and codomain of the evidence are its two endpoint projections. Each projection has at most as many elements as the distinct-pair set. A completed-slot list has at least as many positions as its deduplicated set, so repetitions retain their cost. Support exposure is a necessary condition and is not asserted sufficient.

For the literal two-source relations of PCR.1 and UJB.9001 take the field F with three elements, A = (F² excluding zero) × F² and T = F³ × F². The right endpoint retains every third w coordinate and every z coordinate for both sources. Thus the literal endpoint cardinalities are (9 − 1) × 9 = 72 and 27 × 9 = 243. The label types are seven-bit and eight-bit words, of cardinalities 2⁷ = 128 and 2⁸ = 256. Both ambient inequalities are strict.

The source-zero equations are B₀(v,w) = (v₁w₁ + v₂w₂, v₁w₂ + v₂w₃), and the source-one equations are B₁(v,w) = (v₁w₁ − v₂w₂, v₂w₁ + v₁w₂). Incidence means Bᵢ(v,w) = s and ignores z. UJB Proposition 3.2 and Theorem 15.2 give literal left degree 27 and right degree 8 for each source; these positive degrees supply the two nonisolation hypotheses. They refer to literal endpoints, without replacing either relation by its quotient.

Fix whichever source is actual and supported. Source zero is supported when θ < 1 and source one when θ > 0, with 0 ≤ θ ≤ 1. The prior weight of each full map pair is respectively (1 − θ) or θ divided by (128)₇₂(256)₂₄₃. A transposition changes neither source nor weight positivity. Consequently every same-source competitor constructed here belongs to the original supported family, including at θ = 0 or θ = 1 for the supported branch. No premise comparing the two sources is needed.

A certificate constant over the full supported family is constant over all full embeddings of its actual source. Apply the general theorem to that restricted universal premise, keeping the actual maps and attained distinct positive set D. Its conclusions expose the full images on both sides and yield max(72,243) = 243 ≤ |D| ≤ the number of completed slots. The assertion uses positive complete pairs alone: no absent pair is a negative query and no partially acquired bits or pre-supplied support dictionary enter D.

The generic construction and lower bound are kernel checked. The application requires a canonical Lean identification of the literal UJB relations, their endpoint counts and their degree suppliers; those source-specific suppliers are not provided by this module. Thus this exposition records their parameter correspondence and conditional derivation, and does not assert a compiled theorem for the entire original preparation, positive prior, native acquisition contract or numerical certificate bounds 576 and 324. The abstract target-constancy interpretation agrees with TargetRecoveryCriterion.target_recovery_criterion; the new mathematical input here is the competing full injection, rather than that recovery criterion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.positive_certificate_support_lower_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.transport`
- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.unexposed_left_label_competitor`
- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.unexposed_right_label_competitor`
