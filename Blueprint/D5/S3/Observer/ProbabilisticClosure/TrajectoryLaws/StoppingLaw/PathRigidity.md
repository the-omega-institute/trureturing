# Prefix probabilities reconstruct a detached consecutive path

## Abstract

Prefix probabilities reconstruct a detached consecutive path

Bias consists of a real parameter p strictly between zero and one and different from one half. Its spin masses are pi(false)=1-p and pi(true)=p. Write T(n)=(1-p)^n+p^n and d(n)=T(n)-T(n+1). All finite-spin probabilities refer to one common iid assignment on the finite integer window V.

pathEdges(L,n) is the integer interval from L to L+n-1 and pathVertices(L,n) runs from L to L+n. zeroEdges(E) says that both endpoint spins of every edge in E agree. SupportsEdges requires both endpoints of every listed edge to lie in V. PrefixMasses means that every nonempty prefix of length r has zero-edge probability T(r+1).

**Theorem 1.1 (Every new edge extends an endpoint).**

$$\forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{V} : \operatorname{Finset} (\operatorname{Int})), (\forall (\operatorname{es} : \operatorname{List} (\operatorname{Int})), (((\operatorname{SupportsEdges} (\operatorname{V}, \operatorname{es})) \land (\operatorname{PrefixMasses} (\operatorname{beta}, \operatorname{V}, \operatorname{es})) \land (1 \le \operatorname{length} (\operatorname{es}))) \to ((\operatorname{Nodup} (\operatorname{es})) \land (\exists (\operatorname{L} : \operatorname{Int}), (\operatorname{toFinset} (\operatorname{es}) = \operatorname{pathEdges} (\operatorname{L}, \operatorname{length} (\operatorname{es}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity.prefixes_force_consecutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction appends one edge at a time. A repeated edge retains the old prefix mass. A detached edge gives a strictly different factorized mass. Both alternatives contradict the prescribed next prefix mass, leaving exactly the two adjacent endpoint extensions. Query order need not be monotone.

**Theorem 1.2 (Joint masses also separate the target vertex).**

$$\forall (\operatorname{beta} : \operatorname{Bias}), (\forall (\operatorname{V} : \operatorname{Finset} (\operatorname{Int})), (\forall (\operatorname{es} : \operatorname{List} (\operatorname{Int})), (\forall (\operatorname{q} : \operatorname{Int}), (((1 \le \operatorname{length} (\operatorname{es})) \land (\operatorname{SupportsEdges} (\operatorname{V}, \operatorname{es})) \land (\operatorname{PrefixMasses} (\operatorname{beta}, \operatorname{V}, \operatorname{es})) \land (\forall (\operatorname{s} : \operatorname{Bool}), (\operatorname{prob} (\operatorname{beta}, \operatorname{V}, \operatorname{inter} (\operatorname{zeroEdges} (\operatorname{toFinset} (\operatorname{es})), \operatorname{spinEvent} (\operatorname{q}, \operatorname{s}))) = (\operatorname{pi} (\operatorname{beta}, \operatorname{s}) * \operatorname{T} (\operatorname{beta}, (\operatorname{length} (\operatorname{es}) + 1)))))) \to ((\operatorname{Nodup} (\operatorname{es})) \land (\exists (\operatorname{L} : \operatorname{Int}), ((\operatorname{toFinset} (\operatorname{es}) = \operatorname{pathEdges} (\operatorname{L}, \operatorname{length} (\operatorname{es}))) \land (\operatorname{notMem} (\operatorname{q}, \operatorname{pathVertices} (\operatorname{L}, \operatorname{length} (\operatorname{es})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity.finite_path_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

spinEvent(q,s) is the set of source spins with S(q)=s. If q lay on the recovered path, the two conditional zero-prefix probabilities would force (1-p)^n=p^n for positive n. The biased interior parameter excludes this equality. Both target-spin sections are required.

The finite product factorizations concern the same source realization. Positivity and strict mass gaps hold for every permitted bias; no numerical approximation is used.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity.finite_path_geometry`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity.prefixes_force_consecutive`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization](SemanticNormalization.md)
