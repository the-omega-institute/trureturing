# AmalgamWild

## Abstract

Finite edge-colored graphs and their greedy color-connecting sets.

**Definition 1.1 (starColor).**

$$\forall (\iota \operatorname{A} \operatorname{C} : \operatorname{Type}) (\operatorname{B} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) (\gamma : \forall \operatorname{i} : \iota , (\operatorname{B} \operatorname{i}) . \operatorname{edgeSet} \to \operatorname{C}) , \operatorname{starColor} \operatorname{B} \gamma = (\operatorname{fun} (\operatorname{e} : (\operatorname{AmalgamGraph} . \operatorname{starGraph} \operatorname{B}) . \operatorname{edgeSet}) \mapsto \gamma ((\operatorname{AmalgamGraph} . \operatorname{edgeEquiv} \operatorname{B}) . \operatorname{symm} \operatorname{e}) . 1 ((\operatorname{AmalgamGraph} . \operatorname{edgeEquiv} \operatorname{B}) . \operatorname{symm} \operatorname{e}) . 2)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild.starColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Identifying block roots preserves each block dip. The sorted profile of all other blocks is common to competing edges in one block, so restricting a greedy run preserves its choices.

**Theorem 1.2 (amplify).**

$$\forall (\operatorname{A} \operatorname{C} : \operatorname{Type}) [ \operatorname{Fintype} \operatorname{A} ] [ \operatorname{DecidableEq} \operatorname{A} ] [ \operatorname{Fintype} \operatorname{C} ] (\operatorname{B} : \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) (\gamma : \operatorname{B} . \operatorname{edgeSet} \to \operatorname{C}) , \operatorname{B} . \operatorname{Connected} \to \operatorname{Function} . \operatorname{Surjective} \gamma \to \forall (\operatorname{a} \operatorname{b} : \mathbb{N}) , (\exists \operatorname{O} , \operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{B} \gamma \operatorname{O} \land \operatorname{O} . \operatorname{card} = \operatorname{a}) \to (\forall \operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} (\operatorname{Option} \operatorname{A})) , \operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{B} \gamma \operatorname{W} \to \operatorname{a} \leq \operatorname{W} . \operatorname{card}) \to (\forall \operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} (\operatorname{Option} \operatorname{A})) , \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{B} \gamma \operatorname{W} \to \operatorname{W} . \operatorname{card} = \operatorname{b}) \to \forall \operatorname{r} : \mathbb{N} , 1 \leq \operatorname{r} \to \operatorname{let} \operatorname{Br} : \operatorname{SimpleGraph} (\operatorname{Option} (\operatorname{Fin} \operatorname{r} \times \operatorname{A})) : = \operatorname{AmalgamGraph} . \operatorname{starGraph} (\operatorname{Function} . \operatorname{const} (\operatorname{Fin} \operatorname{r}) \operatorname{B}) ; \operatorname{let} \gamma_{r} : = \operatorname{starColor} (\operatorname{Function} . \operatorname{const} (\operatorname{Fin} \operatorname{r}) \operatorname{B}) (\operatorname{Function} . \operatorname{const} (\operatorname{Fin} \operatorname{r}) \gamma) ; \operatorname{Br} . \operatorname{Connected} \land \operatorname{Function} . \operatorname{Surjective} \gamma_{r} \land \operatorname{Greedy} . \operatorname{wildNumber} \operatorname{Br} \gamma_{r} = \operatorname{a} * \operatorname{r} \land (\exists \operatorname{W} , \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{Br} \gamma_{r} \operatorname{W}) \land (\forall \operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} (\operatorname{Option} (\operatorname{Fin} \operatorname{r} \times \operatorname{A}))) , \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{Br} \gamma_{r} \operatorname{W} \to \operatorname{W} . \operatorname{card} = \operatorname{b} * \operatorname{r})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild.amplify` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifying block roots preserves each block dip. The sorted profile of all other blocks is common to competing edges in one block, so restricting a greedy run preserves its choices.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild.amplify`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild.starColor`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph](AmalgamGraph.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy](Greedy.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/MultisetLex](MultisetLex.md)
