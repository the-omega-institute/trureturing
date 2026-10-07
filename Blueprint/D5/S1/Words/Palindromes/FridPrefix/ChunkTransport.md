# Regroup endpoint paths into six-bit chunks

## Abstract

Regroup endpoint paths into six-bit chunks

**Theorem 1.1 (endpoint_chunked).**

$$\forall us \in List\left(List\left(Fin\left(2\right)\right)\right),\; \forall vs \in List\left(List\left(Fin\left(2\right)\right)\right),\; \left(length\left(us\right) = length\left(vs\right) \land \left(\left(\forall u \in List\left(Fin\left(2\right)\right),\; mem\left(u, us\right) \Rightarrow length\left(u\right) = 6\right) \land \left(\left(\forall v \in List\left(Fin\left(2\right)\right),\; mem\left(v, vs\right) \Rightarrow length\left(v\right) = 6\right) \land mem\left(zip\left(flatten\left(us\right), flatten\left(vs\right)\right), accepts\left(endpoint\right)\right)\right)\right)\right) \Rightarrow mem\left(map\left(\lambda (p:tuple\left(List\left(Fin\left(2\right)\right), List\left(Fin\left(2\right)\right)\right)) \mapsto tuple\left(ofDigits\left(2, map\left(val, reverse\left(fst\left(p\right)\right)\right)\right), ofDigits\left(2, map\left(val, reverse\left(snd\left(p\right)\right)\right)\right)\right), zip\left(us, vs\right)\right), accepts\left(chunkEndpoint\left(6\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/ChunkTransport.endpoint_chunked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nat.ofDigits reads least significant digits first, so each six-bit word is reversed before its digit values are passed to ofDigits. The proof decomposes and rebuilds the actual bit path at each chunk boundary, preserving the initial and terminal states.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ChunkTransport.endpoint_chunked`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton](EndpointAutomaton.md)
