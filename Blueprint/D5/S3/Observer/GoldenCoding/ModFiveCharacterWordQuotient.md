# Mod-Five Character Word Scalar Quotient

## Abstract

The scalar product identifies two distinct directed mod-five character words.

**Theorem 1.1 (The scalar quotient forgets character-word direction).**

$$\begin{aligned}\operatorname{let} characterWord: \operatorname{ZMod}\left(5\right) \to \mathbb{Z} \times \mathbb{Z} = (n: \operatorname{ZMod}\left(5\right) \mapsto (\operatorname{legendreSym}\left(5, \operatorname{val}\left(n\right)\right), \operatorname{legendreSym}\left(5, \operatorname{val}\left(n + 2\right)\right))),\\\operatorname{let} scalarProduct: \mathbb{Z} \times \mathbb{Z} \to \mathbb{Z} = (w: \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{fst}\left(w\right) \times \operatorname{snd}\left(w\right)),\\\operatorname{let} validWords: \operatorname{Finset}\left(\mathbb{Z} \times \mathbb{Z}\right) = \operatorname{image}\left(characterWord, \operatorname{univ}\left(\operatorname{ZMod}\left(5\right)\right)\right),\\(\operatorname{characterWord}\left(1\right) = (1, -1) \land \left(\operatorname{characterWord}\left(2\right) = (-1, 1) \land \left(\operatorname{characterWord}\left(1\right) \ne \operatorname{characterWord}\left(2\right) \land \left(\operatorname{scalarProduct}\left(\operatorname{characterWord}\left(1\right)\right) = -1 \land \left(\operatorname{scalarProduct}\left(\operatorname{characterWord}\left(2\right)\right) = -1 \land \left(\operatorname{scalarProduct}\left(\operatorname{characterWord}\left(1\right)\right) = \operatorname{scalarProduct}\left(\operatorname{characterWord}\left(2\right)\right) \land \left(validWords = \left\{(0, -1), (1, -1), (-1, 1), (-1, 0), (1, 1)\right\} \land \left(\neg \operatorname{InjOn}\left(scalarProduct, \operatorname{coe}\left(validWords\right)\right)\right)\right)\right)\right)\right)\right)\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/ModFiveCharacterWordQuotient.mod_five_character_word_scalar_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For offsets zero and two, the quadratic character modulo five sends residues one and two to the directed words (1,-1) and (-1,1).

The complete residue image is the displayed five-word finite set. The two mixed-sign words are distinct but both have scalar product -1, so pair multiplication is not injective on this character-word image.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/ModFiveCharacterWordQuotient.mod_five_character_word_scalar_quotient`
