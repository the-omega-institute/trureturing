# Labelled Two-Word Unique Decoding

## Abstract

Two labelled words are uniquely decodable exactly when they do not commute.

Fix any universe u and any alphabet alpha of type Type u. A message is a finite list of Boolean labels. Replace false by a and true by b, then concatenate the resulting words. The criterion characterizes injectivity on all finite label lists; it assumes neither decidable equality nor finiteness, inhabitation, or nonemptiness of the alphabet.

**Theorem 1.1 (Exact labelled criterion).**

$$\forall u : \operatorname{Level}\left(\right), \forall alpha : \operatorname{Type}\left(u\right), \forall a : \operatorname{List}\left(alpha\right), \forall b : \operatorname{List}\left(alpha\right), \operatorname{Injective}\left((s : \operatorname{List}\left(\operatorname{Bool}\left(\right)\right) \mapsto \operatorname{flatMap}\left(s, (t : \operatorname{Bool}\left(\right) \mapsto \operatorname{choose}\left(t, a, b\right))\right))\right) \Leftrightarrow a ++ b \neq b ++ a.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/TwoWordCode.injective_iff_noncommuting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula choose(t,a,b) is b when t is true and a when t is false; flatMap performs this substitution followed by concatenation. The symbol ++ denotes list concatenation. Injective compares the label lists themselves, so the two labels remain distinct even when a = b.

An empty codeword prevents injectivity: inserting its label changes the message without changing its encoding. Equal words also prevent it. All these cases commute and are included in the equivalence. Nonempty overlapping words are allowed; for example [false] and [false,true] satisfy the criterion although the first prefixes the second.

If the words commute, the distinct label messages [false,true] and [true,false] have the same encoding. Conversely, descent on the sum of the word lengths removes a shorter nonempty prefix from the longer word. The reduced pair still fails to commute. The substitution false to [false], true to [false,true] transports decoding back to the original pair; its injectivity follows by reversal from prefix-free decoding. When neither word prefixes the other, the original pair is prefix-free and the same decoding theorem applies directly.

This is a mathematical characterization of finite word encodings. It asserts no decoding complexity bound, physical implementation, or literature novelty.

## References

- Truth anchor: `D5/S0/Computability/Coding/TwoWordCode.injective_iff_noncommuting`
