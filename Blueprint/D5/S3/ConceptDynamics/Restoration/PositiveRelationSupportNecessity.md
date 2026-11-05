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

For the literal two-source relations of PCR.1 and UJB.9001 take F = ZMod 3, A = ({v : Fin 2 → F // v ≠ 0}) × (Fin 2 → F), and T = (Fin 3 → F) × (Fin 2 → F). The source relations are Eᵢ = {((v,s),(w,z)) | Bᵢ(v,w) = s}, with B₀(v,w) = (v₁w₁ + v₂w₂, v₁w₂ + v₂w₃) and B₁(v,w) = (v₁w₁ − v₂w₂, v₂w₁ + v₁w₂). The full w₃ coordinate and all nine z values are retained for both sources.

The nonzero v subtype has cardinality 8, so A has cardinality 8 × 9 = 72, and T has cardinality 27 × 9 = 243. The ambient word carriers (Fin 7 → Bool) and (Fin 8 → Bool) have cardinalities 128 and 256. Both source relations have every left and right endpoint incident; their literal edge sets each have 1944 pairs. The strict inequalities 72 < 128 and 243 < 256 provide the unused ambient labels required by the support theorem.

For each nonzero v, each Bᵢ(v,−) takes every s value: there are exactly three w solutions. Each admits all nine z values, giving left degree 27. For fixed (w,z), every one of the eight nonzero v values determines exactly one s, giving right degree 8. In particular left incidence can take any solution w and z = 0; right incidence can take v = (1,0) and s = Bᵢ(v,w). Summing the left degrees gives 72 × 27 = 1944, with no coordinate quotient.

For 0 ≤ θ ≤ 1, a full-map generator at source zero has weight (1 − θ)/((128)₇₂(256)₂₄₃), and a source-one generator has weight θ/((128)₇₂(256)₂₄₃). Thus the zero branch is positive exactly when θ < 1 and the one branch exactly when θ > 0. At θ = 0 only the zero branch is supported; at θ = 1 only the one branch is supported. Any same-source replacement of either full injection keeps the source index and has the same positive prior. The denominator is strictly positive and equals the number of full injection pairs, by Fintype.card_embedding_eq on both carriers.

The exact source application treats a completed history as samples : List ((Fin 7 → Bool) × (Fin 8 → Bool)) and D = samples.toFinset. Each completed pair is positive attained evidence, and target constancy over the supported generator family restricts to the general theorem's universal premise over every full injection pair for the actual source. Attainment already places the actual supported generator in the compatible family, so the constancy premise is not over an empty family. Apply positive_certificate_support_lower_bound with its A replaced by this literal A, its B by T, its L and R by the two word carriers, its E by the actual Eᵢ, and its embeddings by the full λ and ϱ. The source incidence and cardinalities discharge every remaining premise. The two evidence projections equal range λ and range ϱ; max(72,243) = 243 gives 243 ≤ D.card and 243 ≤ samples.length for each supported branch.

This application uses only complete positive pairs. Repetitions remain completed slots, while absent pairs, partial-bit caches, support dictionaries, cross-source identification, and the separate 576- and 324-pair witness constructions are outside this consequence. The source-specific application check is transient evidence for the existing general theorem, with no retained specialization declaration. This establishes the PCR 4.1 support-necessity consequence only; it supplies no preparation procedure, native acquisition contract, or source-bit recovery. The retained mathematical content is the general support and slot lower bound and this scope-limited correspondence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.positive_certificate_support_lower_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.transport`
- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.unexposed_left_label_competitor`
- Truth anchor: `D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.unexposed_right_label_competitor`
