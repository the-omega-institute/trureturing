# Transport of the exact coefficient-one word

## Abstract

Transport of the exact coefficient-one word

**Theorem 1.1 (Transport of the exact coefficient-one word).**

$$\forall (K:\operatorname{Type}),[\operatorname{Field}(K)][\operatorname{Fintype}(K)][\operatorname{CharP}(K,3)]\forall (A:\operatorname{Type}),[\operatorname{AddCommGroup}(A)]\forall (f:\operatorname{AddEquiv}(K\times \operatorname{ZMod}(3),A)),\forall (x:A),\operatorname{f}((0,1))=x\Rightarrow \operatorname{let} M=3\cdot(\operatorname{card}(K)-1);\exists (w:\mathbb{N}\to A),\operatorname{Injective}((i:\operatorname{Fin}(M)\mapsto \operatorname{w}(i)))\land \operatorname{range}((i:\operatorname{Fin}(M)\mapsto \operatorname{w}(i)))=\{y:A|y\neq 0\land y\neq x\land y\neq -x\}\land \operatorname{Injective}((k:\operatorname{Fin}(M)\mapsto \sum_{i<k}\operatorname{w}(i)))\land \sum_{i<M}\operatorname{w}(i)=0\land \forall (a:\mathbb{N}),\forall (b:\mathbb{N}),(a<b\land b\le M\land (a\neq 0\lor b\neq M))\Rightarrow \sum_{a\le i<b}\operatorname{w}(i)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicThreeOrdering.exists_transported_ordering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any finite characteristic-three field, A any additive commutative group, and f an additive equivalence from K times ZMod 3 to A taking (0,1) to x. Put M=3*(card(K)-1). There is a natural-indexed word w whose restriction to Fin M is injective and has range exactly the elements different from 0, x and -x. Its coefficient-one prefixes indexed by Fin M, including the empty prefix and excluding the full prefix, are injective. The full M-term sum is zero. Every nonempty interval [a,b) with 0<=a<b<=M has nonzero sum unless a=0 and b=M. No constraint is placed on values of w beyond the first M terms. The word is the actual successive difference of the field orbit after applying f. Telescoping identifies its n-term prefix with the nth vertex minus the initial vertex. The orbit return proves the full sum is zero, and the orbit bijection separates the first M prefixes. For a terminal interval with b=M and a>0, the terminal vertex is the initial vertex; it cannot equal the proper interior vertex. The label bijection supplies the exact missing-line inventory. A zero first coordinate has row 0, 1 or -1, so f sends that line to exactly 0, x and -x.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicThreeOrdering.exists_transported_ordering`
- Dependency: [D5/S1/Words/Sequenceability/CharacteristicThreeCycle](CharacteristicThreeCycle.md)
