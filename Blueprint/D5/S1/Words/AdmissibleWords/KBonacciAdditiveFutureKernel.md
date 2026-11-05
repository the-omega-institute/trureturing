# Additive responses of actual binary histories

## Abstract

Finite future equality for actual binary histories is characterized by the current additive output, the truncated rejection distance and the available coefficient window.

Let C be a commutative ring, x an element of C, and lambda an additive homomorphism from C to an arbitrary abelian group B. No ring structure on B and no surjectivity or nonzero condition on lambda is required. For the canonical modular probes one takes C to be the image of the single polynomial map into the probe quotients, with x the image of X. This application retains composite moduli and makes no product assertion about the common image.

A history is a finite list of Boolean bits read from low to high degree. Its polynomial value is the sum of x^j over its true positions. The current output is lambda of this value when DBonacciAdmissible accepts the history for the original forbidden run of k true bits, and none otherwise. The scanner has states s in Fin k, resets s to zero on false, increments s on a legal true bit, and rejects at s=k-1. Its partial run composes by Option.bind, so rejection persists under every extension.

Put c_n=lambda(x^n). For two accepted histories w and v, with scanner states s and t and lengths n and m, SignatureEq means all three conditions: their current additive values agree; min(k-s,h+1)=min(k-t,h+1); and c_(n+j)=c_(m+j) for every j<h satisfying s+1<k or j>0. At h=0 the latter conditions are automatic. For positive h the truncated distances already distinguish a terminal tail from a nonterminal tail. A nonterminal tail therefore exposes the entire h-coordinate window; a terminal tail exposes only coordinates one through h-1.

**Theorem 1.1 (The complete finite future signature).**

$$\forall (C: \operatorname{Type}), \forall (B: \operatorname{Type}), [\operatorname{CommRing}\left(C\right)] [\operatorname{AddCommGroup}\left(B\right)], \forall (x: C), \forall (lambda: \operatorname{AddMonoidHom}\left(C, B\right)), \forall (k: \mathbb{N}), 2 \leq k \implies \forall (h: \mathbb{N}), \forall (w: \operatorname{List}\left(\operatorname{Bool}\right)), \forall (v: \operatorname{List}\left(\operatorname{Bool}\right)), \operatorname{NativeKernel}\left(x, lambda, k, h, w, v\right) \iff ((\operatorname{scan}\left(k, w\right) = \operatorname{none}) \land (\operatorname{scan}\left(k, v\right) = \operatorname{none})) \lor (\exists s, \exists t, (\operatorname{scan}\left(k, w\right) = \operatorname{some}\left(s\right)) \land (\operatorname{scan}\left(k, v\right) = \operatorname{some}\left(t\right)) \land (\operatorname{SignatureEq}\left(x, lambda, k, h, w, s, v, t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciAdditiveFutureKernel.actual_history_kernel_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeKernel tests every binary suffix of length at most h, including the empty word and suffixes that lead to rejection. Both rejected histories have equal responses. A rejected history and an accepted history differ already at the empty suffix.

For accepted histories, the proof proceeds by the remaining suffix budget. A false first bit resets both tails and advances both coefficient positions. A true first bit rejects a terminal tail, while a nonterminal tail adds its current coefficient and increments the tail. The empty suffix fixes the current value; additive cancellation recovers the first coefficient whenever a true step is legal. The false branch supplies every later window coordinate. These two branches give necessity and sufficiency of the truncated rejection distance and the stated window, including k=2, h=0 and terminal tails.

The native response is derived from the original scanner on actual concatenated words. Additivity turns the actual polynomial sum into the coefficient sum, and splitting that sum at the history length yields the current value plus the shifted suffix value. No joint realization of independently selected records is assumed by this statement.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciAdditiveFutureKernel.actual_history_kernel_signature`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau](KBonacciActualCommonImagePlateau.md)
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators](KBonacciActualEndpointOperators.md)
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciDirectConcatenation](KBonacciDirectConcatenation.md)
