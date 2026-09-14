# A392714 Phi Tail Encoding

## Abstract

Admissible A392714 permutations produce bounded reversed tail words.

The source permutation fixes the distinguished zero. Read the remaining positions from right to left and subtract n from each value. The resulting integer word has length 2n-1 and uses the residual alphabet strictly between -n and n.

**Theorem 1.1 (Tail length).**

$$\operatorname {length}\left(\operatorname {tailWord}\left(n, p, hn\right)\right) = \operatorname {twoMul}\left(n\right) - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/PhiTailEncoding.tailWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reversed tail is indexed by Fin (2*n-1), so ofFn gives exactly that length.

**Theorem 1.2 (Residual alphabet bounds).**

$$- n < \operatorname {tailWord}\left(n, p, hn\right) < n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/PhiTailEncoding.tailWord_entry_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixing zero and injectivity of a permutation exclude the lower endpoint; the Fin range bound gives the upper endpoint.

**Theorem 1.3 (Bounds for Phi members).**

$$\operatorname {p}\left(inphi\right) \implies \operatorname {residualBounds}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/PhiTailEncoding.mem_phi_tailWord_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in the source finite set supplies the fixed-zero hypothesis, so every tail letter satisfies the same residual bounds.

## References

- Truth anchor: `D5/S1/Words/Compositions/PhiTailEncoding.mem_phi_tailWord_bounds`
- Truth anchor: `D5/S1/Words/Compositions/PhiTailEncoding.tailWord_entry_bounds`
- Truth anchor: `D5/S1/Words/Compositions/PhiTailEncoding.tailWord_length`
- Dependency: [D5/S1/Words/Compositions/AlternatingResidualBridge](AlternatingResidualBridge.md)
