# Local-Law Gluing Obstruction

## Abstract

Pairwise compatible local laws need not admit a joint global state.

**Theorem 1.1 (Compatible local laws can lack a global realization).**

$$\begin{gathered}\operatorname{let} E: \operatorname{Set}(Bool \times Bool) := \{(u, v): Bool \times Bool \mid u = v\},\\{}N: \operatorname{Set}(Bool \times Bool) := \{(u, v): Bool \times Bool \mid u \neq v\}\;\\{}(\operatorname{image}(snd, E) = \operatorname{image}(fst, E) \land\\{}\operatorname{image}(fst, E) = \operatorname{image}(fst, N) \land\\{}\operatorname{image}(snd, E) = \operatorname{image}(snd, N)) \land\\{}(\neg\exists a, b, c: Bool,\\{}(a, b) \in E \land (b, c) \in E \land\\{}(a, c) \in N).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the Boolean pair carrier, E is the equality law and N is the inequality law. Each relevant coordinate projection is the full Boolean carrier, so the three local laws agree on their overlaps.

A global triple would force its first two and last two coordinates to agree while forcing its outer coordinates to differ. The same constructed local laws therefore witness the gluing obstruction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state`
