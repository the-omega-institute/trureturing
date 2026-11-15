# ComponentMirror

## Abstract

Finite edge-colored graphs and their greedy color-connecting sets.

**Definition 1.1 (renameLabels).**

$$\forall (\operatorname{V} : \operatorname{Type}) [ \operatorname{DecidableEq} \operatorname{V} ] (\rho : \operatorname{V} \to \operatorname{V}) (\operatorname{u} \operatorname{v} \operatorname{x} : \operatorname{V}) , \operatorname{renameLabels} \rho \operatorname{u} \operatorname{v} \operatorname{x} = \operatorname{Finset} . \operatorname{piecewise} (\{ \rho \operatorname{u} \} : \operatorname{Finset} \operatorname{V}) (\operatorname{Function} . \operatorname{const} \operatorname{V} (\rho \operatorname{v})) \operatorname{id} (\rho \operatorname{x})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.renameLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components.

**Definition 1.2 (labels).**

$$\forall (\operatorname{V} : \operatorname{Type}) [ \operatorname{DecidableEq} \operatorname{V} ] , (\operatorname{labels} ([ ] : \operatorname{List} (\operatorname{V} \times \operatorname{V})) = \operatorname{id}) \land (\forall (\operatorname{u} \operatorname{v} : \operatorname{V}) (\operatorname{L} : \operatorname{List} (\operatorname{V} \times \operatorname{V})) , \operatorname{labels} (\operatorname{List} . \operatorname{cons} (\operatorname{u} , \operatorname{v}) \operatorname{L}) = \operatorname{renameLabels} (\operatorname{labels} \operatorname{L}) \operatorname{u} \operatorname{v})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.labels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components.

**Definition 1.3 (componentCount).**

$$\forall (\operatorname{V} : \operatorname{Type}) [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] (\operatorname{L} : \operatorname{List} (\operatorname{V} \times \operatorname{V})) , \operatorname{componentCount} \operatorname{L} = (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} (\operatorname{labels} \operatorname{L})) . \operatorname{card}$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.componentCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components.

**Theorem 1.4 (componentCount eq kappa).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] (\operatorname{L} : \operatorname{List} (\operatorname{V} \times \operatorname{V})) , \operatorname{ComponentMirror} . \operatorname{componentCount} \operatorname{L} = \operatorname{Nat} . \operatorname{card} (\operatorname{SimpleGraph} . \operatorname{fromRel} \operatorname{fun} \operatorname{u} \operatorname{v} \mapsto (\operatorname{u} , \operatorname{v}) \in \operatorname{L}) . \operatorname{ConnectedComponent}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.componentCount_eq_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.componentCount`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.componentCount_eq_kappa`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.labels`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.renameLabels`
