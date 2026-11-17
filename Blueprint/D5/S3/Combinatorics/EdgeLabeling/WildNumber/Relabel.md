# Relabel

## Abstract

Finite edge-colored graphs and their greedy color-connecting sets.

**Theorem 1.1 (setMap card).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) , ((\operatorname{fun} \operatorname{f} \operatorname{W} \mapsto \operatorname{Finset} . \operatorname{image} (\operatorname{Sym2} . \operatorname{map} \operatorname{f}) \operatorname{W}) ((\operatorname{DFunLike} . \operatorname{coe} \operatorname{f})) \operatorname{W}) . \operatorname{card} = \operatorname{W} . \operatorname{card}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.setMap_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

**Theorem 1.2 (connecting iff).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] [ \operatorname{Fintype} \operatorname{C} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) (\operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V})) , \operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{H} (\operatorname{SimpleGraph}.\operatorname{EdgeLabeling}.\operatorname{pullback} \gamma (\operatorname{f}.\operatorname{symm}.\operatorname{toHom})) ((\operatorname{fun} \operatorname{f} \operatorname{W} \mapsto \operatorname{Finset} . \operatorname{image} (\operatorname{Sym2} . \operatorname{map} \operatorname{f}) \operatorname{W}) ((\operatorname{DFunLike} . \operatorname{coe} \operatorname{f})) \operatorname{W}) \iff \operatorname{Greedy} . \operatorname{IsColorConnecting} \operatorname{G} \gamma \operatorname{W}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.connecting_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

**Theorem 1.3 (run map).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] [ \operatorname{Fintype} \operatorname{C} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) \{ \operatorname{W} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{V}) \} , \operatorname{Greedy} . \operatorname{IsGreedyRun} \operatorname{G} \gamma \operatorname{W} \to \operatorname{Greedy} . \operatorname{IsGreedyRun} \operatorname{H} (\operatorname{SimpleGraph}.\operatorname{EdgeLabeling}.\operatorname{pullback} \gamma (\operatorname{f}.\operatorname{symm}.\operatorname{toHom})) ((\operatorname{fun} \operatorname{f} \operatorname{W} \mapsto \operatorname{Finset} . \operatorname{image} (\operatorname{Sym2} . \operatorname{map} \operatorname{f}) \operatorname{W}) ((\operatorname{DFunLike} . \operatorname{coe} \operatorname{f})) \operatorname{W})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.run_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

**Theorem 1.4 (setMap surjective).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) , \operatorname{Function} . \operatorname{Surjective} ((\operatorname{fun} \operatorname{f} \operatorname{W} \mapsto \operatorname{Finset} . \operatorname{image} (\operatorname{Sym2} . \operatorname{map} \operatorname{f}) \operatorname{W}) (\operatorname{DFunLike} . \operatorname{coe} \operatorname{f}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.setMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

**Theorem 1.5 (output reflect).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] [ \operatorname{Fintype} \operatorname{C} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) \{ \operatorname{U1} : \operatorname{Finset} (\operatorname{Sym2} \operatorname{U}) \} , \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{H} (\operatorname{SimpleGraph}.\operatorname{EdgeLabeling}.\operatorname{pullback} \gamma (\operatorname{f}.\operatorname{symm}.\operatorname{toHom})) \operatorname{U1} \to \exists \operatorname{W} , (\operatorname{fun} \operatorname{f} \operatorname{W} \mapsto \operatorname{Finset} . \operatorname{image} (\operatorname{Sym2} . \operatorname{map} \operatorname{f}) \operatorname{W}) ((\operatorname{DFunLike} . \operatorname{coe} \operatorname{f})) \operatorname{W} = \operatorname{U1} \land \operatorname{Greedy} . \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{W}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.output_reflect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

**Theorem 1.6 (wildNumber map).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] [ \operatorname{Fintype} \operatorname{C} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) , \operatorname{Greedy} . \operatorname{wildNumber} \operatorname{H} (\operatorname{SimpleGraph}.\operatorname{EdgeLabeling}.\operatorname{pullback} \gamma (\operatorname{f}.\operatorname{symm}.\operatorname{toHom})) = \operatorname{Greedy} . \operatorname{wildNumber} \operatorname{G} \gamma$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.wildNumber_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

**Theorem 1.7 (colorMap surjective).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{U} : \operatorname{Type} \} \{ \operatorname{C} : \operatorname{Type} \} [ \operatorname{Fintype} \operatorname{V} ] [ \operatorname{DecidableEq} \operatorname{V} ] [ \operatorname{Fintype} \operatorname{U} ] [ \operatorname{DecidableEq} \operatorname{U} ] [ \operatorname{Fintype} \operatorname{C} ] \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{U} \} (\operatorname{f} : \operatorname{SimpleGraph} . \operatorname{Iso} \operatorname{G} \operatorname{H}) (\gamma : (\operatorname{CoeSort} . \operatorname{coe} \operatorname{G} . \operatorname{edgeSet}) \to \operatorname{C}) , \operatorname{Function} . \operatorname{Surjective} \gamma \to \operatorname{Function} . \operatorname{Surjective} (\operatorname{SimpleGraph}.\operatorname{EdgeLabeling}.\operatorname{pullback} \gamma (\operatorname{f}.\operatorname{symm}.\operatorname{toHom}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.colorMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph isomorphism carries edge sets and their coloring to the new vertices. Component counts, dip, potential, greedy runs, and the minimum color-connecting cardinality are preserved.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.colorMap_surjective`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.connecting_iff`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.output_reflect`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.run_map`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.setMap_card`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.setMap_surjective`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel.wildNumber_map`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy](Greedy.md)
