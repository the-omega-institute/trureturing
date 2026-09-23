# Fibonacci Word Progression Bound

## Abstract

Bound the longest monochromatic arithmetic progression in the infinite Fibonacci word.

**Definition 1.1 (The global maximum length).**

Lean statement: `D5/S1/Words/FibonacciMapBound.goldenMAPMaximum`

*Formalization.* `D5/S1/Words/FibonacciMapBound.goldenMAPMaximum` (`✓ std3`).

*Citation.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

For each natural difference d, goldenMAPMaximum(d) is the supremum of positive lengths n for which there exist a zero-indexed starting position i and a Boolean letter a such that goldenWord(i+k d)=a for every k<n. True denotes the paper's letter 0 and false denotes letter 1. For positive d the set has a finite attained maximum.

**Theorem 1.2 (Strict bound at every positive difference).**

$$\forall d \in \mathbb{N},\; 0 < d \Rightarrow \frac{goldenMAPMaximum\left(d\right) - 1}{d} < \frac{\sqrt{5}}{\tau}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciMapBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/joshi-rust-fibonacci-map-bound` (proved) by `D5/S1/Words/FibonacciMapBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"joshi-rust-fibonacci-map-bound","declaration_gid":"D5/S1/Words/FibonacciMapBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

The actual word is read at fractional coordinates {(i+k d+1) tau}. For small steps, a monochromatic run cannot wrap across the opposite letter's interval. For large steps, consecutive points of a run occur in alternating clusters, whose two-step displacement limits the length. The irrational quadratic norm of the golden ratio and the integer location of the bound give strictness; the remaining small differences satisfy explicit fractional-window inequalities. The result applies to the attained maximum over all starts and both letters.

## References

- Truth anchor: `D5/S1/Words/FibonacciMapBound.goldenMAPMaximum`
- Truth anchor: `D5/S1/Words/FibonacciMapBound.result`
- Dependency: [D5/S1/Depth/GoldenHurwitzBound](../Depth/GoldenHurwitzBound.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalGoldenBridge](Mechanical/MechanicalGoldenBridge.md)
