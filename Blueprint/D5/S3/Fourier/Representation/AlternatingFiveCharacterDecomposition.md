# Seven-Dimensional A5 Character Decomposition

## Abstract

The source-given A5 character rows verify the seven-dimensional decomposition class by class.

**Theorem 1.1 (The seven-dimensional character is the sum of the 1, 3, and conjugate 3 rows).**

$$\begin{gathered}C := (1A, 2A, 3A, 5A, 5B),\\{}chi_{7} := (7, -1, 1, 2, 2),\\{}chi_{1} := (1, 1, 1, 1, 1),\\{}chi_{3} := (3, -1, 0, \varphi, \psi),\\{}chi_{3'} := (3, -1, 0, \psi, \varphi),\\{}chi_{7} = chi_{1} + chi_{3} + chi_{3'}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Representation/AlternatingFiveCharacterDecomposition.alternating_five_character_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite class type has exactly the labels 1A, 2A, 3A, 5A, and 5B. The four displayed rows are closed definitions of the values stated in the source: the target seven-dimensional character, the trivial character, and the two Galois-conjugate three-dimensional rows.

Pointwise addition gives 1+3+3=7 on 1A, 1-1-1=-1 on 2A, and 1+0+0=1 on 3A. On 5A and 5B, the two golden values are exchanged, and Mathlib's goldenRatio_add_goldenConj identity reduces both sums to 2.

This formalizes the atom's finite character-table verification. The A5 class labels and all character values are source-given data because neither this repository nor pinned Mathlib contains the concrete A5 character table. No representation objects are constructed here, so the result does not independently assert a Lean isomorphism of complex representations.

## References

- Truth anchor: `D5/S3/Fourier/Representation/AlternatingFiveCharacterDecomposition.alternating_five_character_decomposition`
