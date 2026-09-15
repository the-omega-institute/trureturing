# Padding Circuit

## Abstract

Residual padding evolves through one common blank initialized circuit.

**Theorem 1.1 (Residual circuit coefficients).**

$$\operatorname{circuit}\left(\operatorname{U}\left(t\right), n, t, \operatorname{initialized}\left(blank, n, \operatorname{r}\left(b\right)\right), \operatorname{pair}\left(w, k\right)\right) = \operatorname{if}\left(\operatorname{occupation}\left(w\right) = b, \operatorname{f}\left(k\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/PaddingCircuit.circuit_output_of_residuals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and K be finite types, let blank be a symbol of A, and let U be a unitary on A times K. Suppose r assigns a memory vector to each submultiset of a, with r(0)=f. If one application of U to the blank memory state r(b) produces r(b.erase(i)) in coordinate i whenever i occurs in b, and produces zero otherwise, then the length-n circuit coefficient on a word w and memory coordinate k is f(k) exactly when occupation(w)=b.

The statement holds at every starting time and for every legal b. The proof peels the first physical slot, applies the residual transition rule, and inducts on the remaining word length. The empty word is the initialized blank state, and each nonempty word reduces to its tail.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/PaddingCircuit.circuit_output_of_residuals`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../Entanglement/OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../Entanglement/SequentialRegisterCircuit.md)
