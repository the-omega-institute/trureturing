# Golden Character Quotient

## Abstract

The quadratic character modulo five gives a binary quotient of unramified prime words.

**Theorem 1.1 (Golden character quotient specification).**

$$\left(\left(\left(\left(\left(\left(\forall w \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \operatorname{coe}\left(\operatorname{holFiveQuotient}\left(\operatorname{ofList}\left(w\right)\right)\right) = \operatorname{holFive}\left(w\right)\right) \land \left(\forall u \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \forall v \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \operatorname{holFive}\left(\operatorname{append}\left(u, v\right)\right) = \operatorname{holFive}\left(u\right) \cdot \operatorname{holFive}\left(v\right)\right)\right) \land \left(\forall u \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \forall v \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \operatorname{Perm}\left(u, v\right) \Rightarrow \operatorname{holFive}\left(u\right) = \operatorname{holFive}\left(v\right)\right)\right) \land \left(\forall w \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \operatorname{holFive}\left(w\right) = \left(-1\right)^{\operatorname{inertCount}\left(w\right)}\right)\right) \land \left(\forall w \in \operatorname{List}\left(\mathit{UnramifiedPrime}\right),\; \operatorname{holFive}\left(w\right) = 1 \lor \operatorname{holFive}\left(w\right) = -1\right)\right) \land \left(\left(\left(\operatorname{goldenCharacter}\left(\mathit{eleven}\right) = 1 \land \operatorname{goldenCharacter}\left(\mathit{nineteen}\right) = 1\right) \land \operatorname{goldenCharacter}\left(\mathit{two}\right) = -1\right) \land \operatorname{goldenCharacter}\left(\mathit{three}\right) = -1\right)\right) \land \left(\operatorname{holFive}\left(\operatorname{word}\left(\mathit{two}, \mathit{three}\right)\right) = 1 \land \operatorname{holFive}\left(\operatorname{word}\left(\mathit{two}, \mathit{eleven}\right)\right) = -1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient.golden_character_quotient_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict every letter to a rational prime different from five. The Legendre symbol modulo five then takes values in the two integer units, and its product defines a homomorphism from the free monoid of prime words to this binary group.

Concatenation becomes multiplication, permutations do not change the value, and the value is negative one raised to the number of inert letters. The words [2, 3] and [2, 11] witness both quotient values.

The source passage does not define the full holonomy, observer rapidity, or commutator holonomy. No formal claim about forgetting those data is made here.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient.golden_character_quotient_spec`
- Dependency: [D5/S3/Arith/Lattices/RamifiedFiveBoundarySelection](../../Arith/Lattices/RamifiedFiveBoundarySelection.md)
