# Finite original-view reconstruction

## Abstract

The original rational, chronological word, rooted named path and indexed memory retain one another exactly.

The root pair is (1,1). L sends (p,q) to (p,p+q) and R sends it to (p+q,q). encode executes the head first. The decoder subtracts the smaller positive coordinate from the larger and appends the peeled last letter to the recursively decoded predecessor. Every recursive step decreases p+q. The input rational uses its reduced positive numerator and denominator, and all inverse arithmetic is on this known output pair.

**Theorem 1.1 (Actual-image finite inverses).**

$$(\forall p,q\in\mathbb{N}, 0<p\land0<q\land\operatorname{Coprime}\left(p, q\right)\longrightarrow\operatorname{encode}\left(\operatorname{decode}\left(p, q\right)\right)=(p,q))\land (\forall w,\operatorname{decode}\left(\operatorname{encode}\left(w\right)\right)=w)\land (\forall V,x,0<x\longrightarrow \operatorname{recover}\left(V, \operatorname{original}\left(V, x\right)\right)=x)\land (\forall w,\operatorname{ratio}\left(\operatorname{encode}\left(w\right)\right)=\operatorname{attain}\left(w, 1\right))\land (\forall w,\operatorname{originalWord}\left(\operatorname{ratio}\left(\operatorname{encode}\left(w\right)\right)\right)=w)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/Views.original_views_reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive coprime pair the encoder of its decoded chronological word is that same pair. For every finite Boolean word the decoded encoded pair is that very word, including the empty word. Its pair ratio equals the attained response of the actual chronological source started at 1, and decoding that ratio returns the same word.

For every positive rational x, each of B,T,S,M and their full joint output has a finite decoder returning x. B is x itself. T is its entire chronological word. S retains the distinguished root occurrence (0,(1,1)), the indexed final occurrence, and every oriented edge with its name, source index, target index and both endpoint pairs. M retains every indexed prefix pair from index 0 through the original word length. The full output contains all four. Equal numeric vertex values do not collapse occurrence indices or edge names.

The path decoder reads the edge names in their rooted orientation. The memory decoder reads its final indexed pair, rather than replacing the table by a scalar length. The constructions and decoders are finite computations on their actual images. Composing the rational decoder of one view with the construction of another gives the corresponding actual-image transport in either direction. No unknown archive, acquired infinite thread, extra source motion or inverse physical action is used.

## References

- Truth anchor: `D5/S3/Observer/RationalRouting/Views.original_views_reconstruct`
- Dependency: [D5/S3/Observer/RationalRouting/Source](Source.md)
