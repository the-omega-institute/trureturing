# MultisetLex

## Abstract

Finite edge-colored graphs and their greedy color-connecting sets.

**Theorem 1.1 (sort add lex iff).**

$$\forall (\operatorname{s} \operatorname{t} \operatorname{u} : \operatorname{Multiset} \mathbb{N}) , \operatorname{List} . \operatorname{Lex} (\operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} < \operatorname{x2}) ((\operatorname{s} + \operatorname{u}) . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \geq \operatorname{x2}) ((\operatorname{t} + \operatorname{u}) . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \geq \operatorname{x2}) \iff \operatorname{List} . \operatorname{Lex} (\operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} < \operatorname{x2}) (\operatorname{s} . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \geq \operatorname{x2}) (\operatorname{t} . \operatorname{sort} \operatorname{fun} \operatorname{x1} \operatorname{x2} \mapsto \operatorname{x1} \geq \operatorname{x2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/MultisetLex.sort_add_lex_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sorting natural-number multisets in nonincreasing order gives a lexicographic comparison that is preserved and reflected by addition of a common multiset.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/MultisetLex.sort_add_lex_iff`
