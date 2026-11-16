# Reflection orbits and a marked bi-infinite mirror

## Abstract

Marked mirrors transfer bounded factor increments to reflection increments.

**Theorem 1.1 (Counting the surplus in finite fibers).**

$$\forall X: \operatorname{Type}, \forall Y: \operatorname{Type}, [\operatorname{DecidableEq}\left(Y\right)] \forall a: \operatorname{Finset}\left(X\right), \forall f: X \to Y, \sum_{y \in \operatorname{Finset.image}\left(f, a\right)} \operatorname{Nat.sub}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left((x: X \mapsto f\left(x\right) = y), a\right)\right), 1\right) = \operatorname{Nat.sub}\left(\operatorname{Finset.card}\left(a\right), \operatorname{Finset.card}\left(\operatorname{Finset.image}\left(f, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.fiberSurplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing each nonempty fiber's cardinality minus one gives the domain cardinality minus the image cardinality. Both subtractions are natural subtraction.

**Definition 1.2 (Reflection equivalence).**

$$\forall A: \operatorname{Type}, \forall n: \mathbb{N}, \forall u: \operatorname{Fin}\left(n\right) \to A, \forall v: \operatorname{Fin}\left(n\right) \to A, \operatorname{ReflectivelyEquivalent}\left(u, v\right) = \left((v = u) \lor (v = \operatorname{Function.comp}\left(u, \operatorname{Fin.rev}\right))\right)$$

*Formalization.* `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.ReflectivelyEquivalent` (`✓ std3`).

*Citation.* Jean-Paul Allouche; John M. Campbell; Shuo Li; Jeffrey Shallit; Manon Stipulanti (2025). *The reflection complexity of sequences over finite alphabets*. DOI: [10.1007/s00224-025-10234-x](https://doi.org/10.1007/s00224-025-10234-x). URL: <https://arxiv.org/abs/2406.09302v4>.

*Commentary.*

Definition 1, p. 3: “Two finite words u and v are reflectively equivalent if v = u or v = uᴿ.” The alphabet is arbitrary, and Fin.rev reverses the zero-based positions of a word of length n.

**Definition 1.3 (Counting classes of actual factors).**

$$\forall A: \operatorname{Type}, [\operatorname{Fintype}\left(A\right)] \forall x: \mathbb{N} \to A, \forall n: \mathbb{N}, \operatorname{reflectionComplexity}\left(x, n\right) = \operatorname{Nat.card}\left(\operatorname{Quot}\left((u: \operatorname{Subtype}\left((w: \operatorname{Fin}\left(n\right) \to A \mapsto w \in \operatorname{wordFactorSet}\left(x, n\right))\right) \mapsto (v: \operatorname{Subtype}\left((w: \operatorname{Fin}\left(n\right) \to A \mapsto w \in \operatorname{wordFactorSet}\left(x, n\right))\right) \mapsto \operatorname{ReflectivelyEquivalent}\left(\operatorname{val}\left(u\right), \operatorname{val}\left(v\right)\right)))\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.reflectionComplexity` (`✓ std3`).

*Citation.* Jean-Paul Allouche; John M. Campbell; Shuo Li; Jeffrey Shallit; Manon Stipulanti (2025). *The reflection complexity of sequences over finite alphabets*. DOI: [10.1007/s00224-025-10234-x](https://doi.org/10.1007/s00224-025-10234-x). URL: <https://arxiv.org/abs/2406.09302v4>.

*Commentary.*

Definition 3, p. 3: “Let x be a sequence. The reflection complexity function rₓ : ℕ₀ → ℕ of x maps every n ≥ 0 to the number of distinct length-n factors of x, up to equivalence by ∼ᵣ.” The quotient is taken over the occurring factors themselves, without assuming reversal closure. The empty factor contributes one class. Example 4 counts the Thue–Morse length-two classes represented by 00, 11 and either of 01 and 10, giving three.

**Definition 1.4 (A single marker between two mirror images).**

$$\forall A: \operatorname{Type}, \forall x: \mathbb{N} \to A, \forall i: \mathbb{Z}, \operatorname{mirrorWord}\left(x, i\right) = \operatorname{if} (i = 0) \operatorname{then} \operatorname{none} \operatorname{else} \operatorname{some}\left(x\left(\operatorname{Nat.sub}\left(\operatorname{Int.natAbs}\left(i\right), 1\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.mirrorWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The new letter is Option.none. At every nonzero integer position, Option.some carries the source letter indexed by the natural absolute value minus one. Natural subtraction is truncated; the subtraction is evaluated only away from the marker.

**Definition 1.5 (Factors at integer starts).**

$$\forall A: \operatorname{Type}, \forall z: \mathbb{Z} \to \operatorname{Option}\left(A\right), \forall n: \mathbb{N}, \forall i: \mathbb{Z}, \operatorname{intFactor}\left(z, n, i\right) = (k: \operatorname{Fin}\left(n\right) \mapsto z\left(i + (\operatorname{val}\left(k\right): \mathbb{Z})\right))$$

*Formalization.* `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.intFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A factor at i reads the bi-infinite word at i plus each finite position, with that position coerced to the integers.

**Definition 1.6 (The bi-infinite factor set).**

$$\forall A: \operatorname{Type}, [\operatorname{Fintype}\left(A\right)] \forall z: \mathbb{Z} \to \operatorname{Option}\left(A\right), \forall n: \mathbb{N}, \operatorname{intFactorSet}\left(z, n\right) = \operatorname{Finset.filter}\left((w: \operatorname{Fin}\left(n\right) \to \operatorname{Option}\left(A\right) \mapsto \exists i: \mathbb{Z}, w = \operatorname{intFactor}\left(z, n, i\right)), \operatorname{Finset.univ}\right)$$

*Formalization.* `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.intFactorSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains exactly those functions on Fin n that occur at some integer start.

**Theorem 1.7 (Linear growth survives the marked mirror).**

$$\forall A: \operatorname{Type}, [\operatorname{Fintype}\left(A\right)] \forall x: \mathbb{N} \to A, \forall C: \mathbb{N}, (\forall k: \mathbb{N}, \operatorname{Finset.card}\left(\operatorname{wordFactorSet}\left(x, k\right)\right) \le C \cdot \left(k + 1\right)) \Rightarrow (\forall n: \mathbb{N}, \operatorname{Finset.card}\left(\operatorname{intFactorSet}\left(\operatorname{mirrorWord}\left(x\right), n\right)\right) \le \left(2 \cdot C + 1\right) \cdot \left(n + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.mirrorFactorLinear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A length-n factor avoiding the marker is a source factor or its reversal. Factors containing the marker have n distinct marker positions. Thus the exact mirror count is the size of the reversal-symmetrized factor set plus n, including n = 0. A source bound C times (n + 1) therefore gives mirror coefficient 2 times C plus 1.

**Theorem 1.8 (Bounded mirror increments bound reflection increments).**

$$\forall A: \operatorname{Type}, [\operatorname{Fintype}\left(A\right)] \forall x: \mathbb{N} \to A, \forall D: \mathbb{N}, (\forall k: \mathbb{N}, \operatorname{Finset.card}\left(\operatorname{intFactorSet}\left(\operatorname{mirrorWord}\left(x\right), k + 1\right)\right) \le \operatorname{Finset.card}\left(\operatorname{intFactorSet}\left(\operatorname{mirrorWord}\left(x\right), k\right)\right) + D) \Rightarrow (\exists B: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{Int.natAbs}\left((\operatorname{reflectionComplexity}\left(x, n + 1\right): \mathbb{Z}) - (\operatorname{reflectionComplexity}\left(x, n\right): \mathbb{Z})\right) \le B)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.reflectionBoundOfMirrorBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q for reflection complexity, u for the reversal-symmetrized factor count and P for its palindromic count. Counting reflection orbits gives 2q = u + P. A sliding factor walk visits all reflection classes; deleting the distinct palindromic loops preserves connectivity and gives q(n) + P(n + 1) ≤ q(n + 1) + 1. Combining these counts with the exact mirror formula bounds the integer absolute difference by D + 1.

## References

- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.ReflectivelyEquivalent`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.fiberSurplus`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.intFactor`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.intFactorSet`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.mirrorFactorLinear`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.mirrorWord`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.reflectionBoundOfMirrorBound`
- Truth anchor: `D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.reflectionComplexity`
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
