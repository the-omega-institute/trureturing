# First Starts at Fibonacci Differences

## Abstract

Locate the first longest monochromatic progression at every Fibonacci difference.

**Definition 1.1 (The first start of a longest progression).**

$$\forall d \in \mathbb{N},\; goldenMAPFirstStart\left(d\right) = sInf\left(\{j \in \mathbb{N} \mid (\exists c \in Bool,\; \forall k \in \mathbb{N},\; k < goldenMAPMaximum\left(d\right) \Rightarrow goldenWord\left(j + k \cdot d\right) = c)\}\right)$$

*Formalization.* `D5/S1/Words/FibonacciMapFirstStart.goldenMAPFirstStart` (`✓ std3`).

*Citation.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

goldenWord is the zero-indexed fixed point 010010100100101... of 0 -> 01 and 1 -> 0. True represents 0 and false represents 1. goldenMAPMaximum(d) is the supremum of all positive progression lengths over every natural start and both letters. The definition takes the natural infimum of starts attaining that length, without choosing a letter in advance. At the Fibonacci differences below the length set is bounded and its maximum is attained, so the start set is nonempty and its infimum is its least element.

**Theorem 1.2 (Both parity families).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (goldenMAPFirstStart\left(fib\left(2 \cdot n + 1\right)\right) = fib\left(2 \cdot n + 3\right) - 2 \land goldenMAPFirstStart\left(fib\left(2 \cdot n\right)\right) = fib\left(4 \cdot n\right) - 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/FibonacciMapFirstStart.result` (`✓ std3`). ∎

*Resolves.* `Problems/joshi-rust-fibonacci-map-first-start` (proved) by `D5/S1/Words/FibonacciMapFirstStart.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"joshi-rust-fibonacci-map-first-start","declaration_gid":"D5/S1/Words/FibonacciMapFirstStart.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gandhar Joshi and Dan Rust (2025). *Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words*. DOI: [10.1016/j.tcs.2025.115391](https://doi.org/10.1016/j.tcs.2025.115391). URL: <https://arxiv.org/html/2501.05830v2>.

*Commentary.*

Here fib is the natural Fibonacci sequence, with fib(0)=0 and fib(1)=1. For every n at least one both differences are positive. The two equations describe the earliest starts attaining the global maximum, not just starts of particular progression witnesses.

Write r=1/tau and m for the Fibonacci index. At word position j the phase is {(j+1)tau}, and true letters occupy (r^2,1). The step is r^m to the right for odd m and r^m to the left for even m. The natural maximum length is fib(m-2)+fib(m) for odd m and one more for even m. Open symbol endpoints prevent wraparound even when m=2 and the step equals r^2. Every false-letter progression is strictly shorter.

Cassini's integer determinant gives one-sided orbit records: before fib(m+2), the positive displacement for odd m, or the backward displacement for even m, is at least r^m. In integral Fibonacci coordinates a smaller displacement would force a denominator at least fib(m)+fib(m+1). The odd maximal-start interval translates by one extra rotation to a positive interval shorter than r^m. The even interval has backward width r^(2m-1), smaller than the preceding even record r^(2m-2). These exclusions rule out every earlier start. The boundary n=1 gives first starts 3 at difference 2 and 2 at difference 1.

## References

- Truth anchor: `D5/S1/Words/FibonacciMapFirstStart.goldenMAPFirstStart`
- Truth anchor: `D5/S1/Words/FibonacciMapFirstStart.result`
- Dependency: [D5/S1/Deficit/Displacement/GoldenSubstStartSharpness](../Deficit/Displacement/GoldenSubstStartSharpness.md)
- Dependency: [D5/S1/Words/FibonacciMapBound](FibonacciMapBound.md)
