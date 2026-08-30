# Completion Locus Calculus

## Abstract

Structural completion loci compose by intersection, pull back along arbitrary parameter maps, and retain gauge stability under conjunction.

**Theorem 1.1 (Completion Locus Pair eq Inter).**

$$\forall A: Type, D_{1}: Type, D_{2}: Type, normalization_{1}: Set A, normalization_{2}: Set A, defect_{1}: A \to D_{1}, defect_{2}: A \to D_{2}, zero_{1}: D_{1}, zero_{2}: D_{2},\\{}(completionPointSet (normalization_{1} intersection normalization_{2}) (\lambda a \mapsto (defect_{1} a, defect_{2} a)) (zero_{1}, zero_{2}) = completionPointSet normalization_{1} defect_{1} zero_{1} intersection completionPointSet normalization_{2} defect_{2} zero_{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_pair_eq_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjoining two normalizations and pairing their defects gives exactly the intersection of their completion loci.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Completion Locus Preimage).**

$$\forall A: Type, A': Type, D: Type, parameterMap: A' \to A, normalization: Set A, defect: A \to D, zeroD: D,\\{}(completionPointSet (parameterMap ^{-1} normalization) (defect \circ parameterMap) zeroD = parameterMap ^{-1} (completionPointSet normalization defect zeroD)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Completion loci pull back exactly along arbitrary parameter maps.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Completion Locus Intersection Gauge Stable).**

$$\forall G: Type, A: Type, D_{1}: Type, D_{2}: Type, normalization_{1}: Set A, normalization_{2}: Set A, defect_{1}: A \to D_{1}, defect_{2}: A \to D_{2}, zero_{1}: D_{1}, zero_{2}: D_{2}, [\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, A\right)],\\{}(\forall (g : G) \{a : A\}, a \in completionPointSet normalization_{1} defect_{1} zero_{1} \Rightarrow g \cdot a \in completionPointSet normalization_{1} defect_{1} zero_{1}) \land (\forall (g : G) \{a : A\}, a \in completionPointSet normalization_{2} defect_{2} zero_{2} \Rightarrow g \cdot a \in completionPointSet normalization_{2} defect_{2} zero_{2}) \Rightarrow\\{}(\forall (g : G) \{a : A\}, a \in completionPointSet (normalization_{1} intersection normalization_{2}) (\lambda value \mapsto (defect_{1} value, defect_{2} value)) (zero_{1}, zero_{2}) \Rightarrow g \cdot a \in completionPointSet (normalization_{1} intersection normalization_{2}) (\lambda value \mapsto (defect_{1} value, defect_{2} value)) (zero_{1}, zero_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_intersection_gauge_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two completion loci are stable under the same gauge action, their conjoined locus is stable as well.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_intersection_gauge_stable`
- Truth anchor: `D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_pair_eq_inter`
- Truth anchor: `D5/S3/Observer/Completion/CompletionLocusCalculus.completion_locus_preimage`
- Dependency: [D5/S3/Observer/Completion/StructuralCompletionSignature](StructuralCompletionSignature.md)
