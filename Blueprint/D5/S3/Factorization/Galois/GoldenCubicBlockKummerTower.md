# Lucas-Block Kummer Tower Degree

## Abstract

Every cubic-root tower built from the actual Lucas blocks has degree three to the number of stages.

**Theorem 1.1 (Every Lucas-block cubic-root tower has degree three to the number of stages).**

$$\begin{aligned}K := \operatorname{CyclotomicField}\left(3, \mathbb{Q}\right), A := \operatorname{AlgebraicClosure}\left(K\right),\\B_{j} := \operatorname{natAbs}\left(\left(L_{3^{j}}\right)^{2}+3\right),\\\operatorname{tower}\left(\beta, 0\right) := K, \forall m \in \mathbb{N}, \operatorname{tower}\left(\beta, m+1\right) := \operatorname{tower}\left(\beta, m\right)(\beta_{m+1}),\\\forall \beta: \mathbb{N} \to A, (\forall j \in \mathbb{N}, 1 \le j \Rightarrow \left(\beta_{j}\right)^{3} = \operatorname{algebraMap}\left(K, A, B_{j}\right)) \Rightarrow\\\forall J \in \mathbb{N}, [\operatorname{tower}\left(\beta, J\right):K] = 3^{J}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base is the third cyclotomic field over the rationals, and the ambient field is its algebraic closure. The block is the natural absolute value of the Lucas expression L at index 3 to the j, squared, plus three; that expression is positive. The roots at positive indices may be any cubic roots of their blocks. The root at index zero is unused.

The integer noncube and pairwise coprimality results for the actual blocks keep each new block from becoming a cube in the preceding tower. Cubic Galois descent transports a hypothetical cube down one stage, while coprimality prevents cancellation by an earlier block. The cubic polynomial is then irreducible at each stage, and the degrees multiply.

The statement includes the empty tower at J equal to zero. It gives the degree over the third cyclotomic field for every admissible choice of cubic roots; it does not select positive real roots or assert a discriminant, ramification law, or Galois-group classification.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicBlockKummerTower.golden_cubic_block_kummer_tower_degree`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods](../../Arith/Primes/GoldenCubicBlockNativePowerPeriods.md)
- Dependency: [D5/S3/Factorization/GoldenCubicBlockNoncube](../GoldenCubicBlockNoncube.md)
