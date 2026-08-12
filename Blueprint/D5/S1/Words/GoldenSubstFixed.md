# Pointwise Substitution Fixed Point of the Golden Word

## Abstract

Locate consecutive Fibonacci-substitution blocks and identify each block pointwise with the infinite golden word.

**Definition 1.1 (True-count partial sums locate substitution block starts).**

$$\operatorname{goldenSubstStart}(i)=i+\operatorname{goldenWindowTrueCount}(0,i)$$

*Formalization.* `D5/S1/Words/GoldenSubstFixed.goldenSubstStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of each true letter has length two, while the image of each false letter has length one. The block for source index i therefore starts at i plus the number of true letters strictly before i.

**Theorem 1.2 (Consecutive substitution blocks meet at their boundaries).**

$$\forall i\in\mathbb{N},\ \operatorname{goldenSubstStart}(i+1)=\operatorname{goldenSubstStart}(i)+\operatorname{length}(\operatorname{subst}(\operatorname{goldenWord}(i)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenSubstFixed.goldenSubstStart_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Advancing one source index adds exactly the length of that letter's substitution image. Thus the computed boundaries are consecutive, with neither gaps nor overlaps between adjacent image blocks.

**Theorem 1.3 (Every substituted source block agrees pointwise with the golden word).**

$$\forall i\in\mathbb{N},\ \forall j\in\operatorname{Fin}(\operatorname{length}(\operatorname{subst}(\operatorname{goldenWord}(i)))),\ \operatorname{goldenWord}(\operatorname{goldenSubstStart}(i)+j)=\operatorname{get}(\operatorname{subst}(\operatorname{goldenWord}(i)),j)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenSubstFixed.golden_word_substitution_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source index i and every valid offset j in its substitution image, the infinite golden word at the computed block position equals the j-th image letter. The proof identifies the corresponding block in a finite Fibonacci-word substitution and then passes to the diagonal golden-word limit; it requires no global output-to-source inverse.

## References

- Truth anchor: `D5/S1/Words/GoldenSubstFixed.goldenSubstStart`
- Truth anchor: `D5/S1/Words/GoldenSubstFixed.goldenSubstStart_succ`
- Truth anchor: `D5/S1/Words/GoldenSubstFixed.golden_word_substitution_fixed`
- Dependency: [D5/S1/Words/GoldenWord](GoldenWord.md)
