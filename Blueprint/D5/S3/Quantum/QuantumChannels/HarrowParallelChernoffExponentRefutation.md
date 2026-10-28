# A product-state bound excludes parallel exponent one

## Abstract

For every positive number of parallel uses, the product state with qubits zero and one gives an error exponent at least two, excluding convergence to one.

The input factors are ordered A, C. MatrixMap denotes complex linear maps between matrix spaces, and all matrices below have complex entries. Finite enumerations and decidable equality are supplied by the anonymous bracketed assumptions. ENNReal is the nonnegative extended real line, with truncated subtraction, and EReal is the extended real line with both infinities. Source line numbers refer to cq-channel-PRXQ-revised.14jan22mh+aw.tex in arXiv:2011.06569v3.

**Definition 1.1 (The first channel).**

$$\forall (x: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (c: \operatorname{Fin}\left(2\right)), (\forall (d: \operatorname{Fin}\left(2\right)), (\operatorname{harrowM}\left(x, c, d\right) = \operatorname{ite}\left(c = d, \operatorname{ite}\left(c = (0: \operatorname{Fin}\left(2\right)), x\left(((0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))\right) + x\left(((1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))\right) + x\left(((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right), (0: \mathbb{C})\right) + \frac{x\left(((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right)}{(2: \mathbb{C})}, (0: \mathbb{C})\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.harrowM` (`✓ std3`).

*Citation.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

This is the first channel of Example 5, source lines 1406-1417, extended linearly to every matrix x. The output is diagonal. The first three computational basis inputs contribute to the zero output, while the input with both qubits one contributes half its diagonal entry to each output diagonal entry. The formula specifies every entry, including both off-diagonal output entries.

**Definition 1.2 (The second channel).**

$$\forall (x: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (c: \operatorname{Fin}\left(2\right)), (\forall (d: \operatorname{Fin}\left(2\right)), (\operatorname{harrowMbar}\left(x, c, d\right) = \frac{x\left(((0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))\right) + x\left(((1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))\right)}{(2: \mathbb{C})} + \operatorname{ite}\left((c = (1: \operatorname{Fin}\left(2\right))) \land (d = (1: \operatorname{Fin}\left(2\right))), \frac{x\left(((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right) + x\left(((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right) + x\left(((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right) + x\left(((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right)}{(2: \mathbb{C})}, (0: \mathbb{C})\right) + \operatorname{ite}\left(c = d, \frac{x\left(((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right) - x\left(((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right) - x\left(((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right) + x\left(((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))\right)}{(4: \mathbb{C})}, (0: \mathbb{C})\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.harrowMbar` (`✓ std3`).

*Citation.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

This is the second channel of Example 5, source lines 1413-1419. When C is zero, the Hadamard plus state gives the same contribution to all four output entries. When C is one, the Hadamard plus outcome on A contributes to the one output and the minus outcome contributes to the maximally mixed output. The off-diagonal entries of x in the C-equals-one block therefore occur with the displayed signs.

**Definition 1.3 (Tensor powers on matrix units).**

$$\forall (\iota: \operatorname{Type}), (\forall (\kappa: \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], [\operatorname{Fintype}\left(\kappa\right)], \forall (\varphi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\iota, \kappa, \mathbb{C}\right)), (\forall (n: \mathbb{N}), (\forall (x: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\iota), (\operatorname{Fin}\left(n\right)) \to (\iota), \mathbb{C}\right)), (\forall (c: (\operatorname{Fin}\left(n\right)) \to (\kappa)), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\kappa)), (\operatorname{tensorPow}\left(\varphi, n, x, c, d\right) = \sum_{a: (\operatorname{Fin}\left(n\right)) \to (\iota)} (\sum_{b: (\operatorname{Fin}\left(n\right)) \to (\iota)} (x\left(a, b\right) \cdot \prod_{k: \operatorname{Fin}\left(n\right)} (\varphi\left(\operatorname{Matrix.single}\left(a\left(k\right), b\left(k\right), (1: \mathbb{C})\right), c\left(k\right), d\left(k\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.tensorPow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

The n-fold tensor power is specified on matrix units and extended linearly. For every pair a, b of input strings, its matrix-unit image has entry equal to the product of the n single-copy entries. Summing these images with coefficients x(a,b) defines the map on arbitrary matrices. The empty product also defines the zeroth tensor power. This is a finite-coordinate realization of the tensor powers appearing at source lines 1300-1306.

**Definition 1.4 (Stabilized trace-norm supremum).**

$$\forall (\iota: \operatorname{Type}), (\forall (\kappa: \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)], [\operatorname{DecidableEq}\left(\iota\right)], [\operatorname{Fintype}\left(\kappa\right)], \forall (\varphi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\iota, \kappa, \mathbb{C}\right)), ((\operatorname{diamondNorm}\left(\varphi\right): \operatorname{ENNReal}) = \operatorname{sSup}\left(\{(r: \operatorname{ENNReal}) \mid \exists (\rho: \operatorname{Matrix}\left((\iota \times \iota), (\iota \times \iota), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \land ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \land (r = \operatorname{ENNReal.ofReal}\left(\operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left(\operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron}\left(\varphi, (\operatorname{LinearMap.id}: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\iota, \iota, \mathbb{C}\right)), \rho\right)\right)\right))))\}\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.diamondNorm` (`✓ std3`).

*Citation.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

The reference system has the same index type as the input. The supremum ranges over every positive semidefinite matrix rho of trace one on the input and reference. Applying phi to the input and the identity to the reference gives a matrix whose trace norm is included into ENNReal by ENNReal.ofReal. This is the density-matrix optimization for the diamond norm in the discrimination formula at source lines 1273-1295. The definition makes sense for every complex linear matrix map; here it is used for differences of tensor powers of the two channels.

**Definition 1.5 (Equal-prior parallel error).**

$$\forall (n: \mathbb{N}), ((\operatorname{parallelError}\left(n\right): \operatorname{ENNReal}) = \operatorname{HDiv.hDiv}\left(((1: \operatorname{ENNReal}) - \operatorname{HDiv.hDiv}\left((\operatorname{diamondNorm}\left(\operatorname{tensorPow}\left(\operatorname{harrowM}, n\right) - \operatorname{tensorPow}\left(\operatorname{harrowMbar}, n\right)\right): \operatorname{ENNReal}), (2: \operatorname{ENNReal})\right): \operatorname{ENNReal}), (2: \operatorname{ENNReal})\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.parallelError` (`✓ std3`).

*Citation.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

The equal-prior error probability is half of one minus half the stabilized norm of the channel difference, as at source lines 1303-1306. The expression is evaluated in ENNReal, including its truncated subtraction and extended division, for every natural n. The named HDiv.hDiv applications denote ENNReal division on explicitly typed operands. Fraction notation is reserved for complex or real field division.

**Definition 1.6 (The base-two error exponent).**

$$\forall (n: \mathbb{N}), ((\operatorname{exponent}\left(n\right): \operatorname{EReal}) = \operatorname{Real.toEReal}\left((\operatorname{Inv.inv}\left((\operatorname{Nat.cast}\left(n\right): \mathbb{R}) \cdot \operatorname{Real.log}\left((2: \mathbb{R})\right)\right): \mathbb{R})\right) \cdot \left(-\operatorname{ENNReal.log}\left(\operatorname{parallelError}\left(n\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.exponent` (`✓ std3`).

*Citation.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

Real.log and ENNReal.log use natural logarithms. Division by Real.log 2 gives the base-two convention specified at source lines 894-896 and used for the exponent at lines 1308-1315. The natural n is explicitly cast to a real number; the real inverse normalization is then included into EReal by Real.toEReal. For positive n, zero error has exponent positive infinity. The definition also assigns a value at n equal to zero using the extended-real arithmetic conventions.

**Definition 1.7 (The proposed limit one).**

$$(\operatorname{claim}) \Leftrightarrow (\operatorname{Filter.Tendsto}\left(\operatorname{exponent}, \operatorname{Filter.atTop}, \operatorname{nhds}\left((1: \operatorname{EReal})\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

The proposition says that exponent tends to one in EReal as the natural number of parallel uses tends to infinity. It expresses the optimality conjecture at source lines 1510-1514 for the two explicit channels above. It neither assumes positive error at every n nor replaces the infinite exponent of zero error by a finite value.

**Theorem 1.8 (The limit cannot be one).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/salek-hayashi-winter-2020-harrow-parallel-chernoff-exponent` (refuted) by `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"salek-hayashi-winter-2020-harrow-parallel-chernoff-exponent","declaration_gid":"D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Farzin Salek; Masahito Hayashi; Andreas Winter (2022). *Usefulness of adaptive strategies in asymptotic quantum channel discrimination*. DOI: [10.1103/PhysRevA.105.022419](https://doi.org/10.1103/PhysRevA.105.022419). URL: <https://arxiv.org/abs/2011.06569v3>.

*Commentary.*

First evaluate both channels on the matrix unit at the computational basis pair (0,1). The first output is diagonal with entries 1 and 0, and the second is diagonal with entries 1/4 and 3/4. Next, expanding the tensor-power sums on an arbitrary matrix unit leaves precisely the product of its single-copy entries. If each single-copy output is diagonal, the product output is diagonal too: two unequal output strings differ at some coordinate, where the corresponding off-diagonal factor vanishes.

Apply these identities to the constant string of pairs (0,1). For an output string c, let its real weight be the product over coordinates k of 1/4 when c(k) is zero and 3/4 otherwise. The tensor-power channel difference on this matrix unit is diagonal, with entry one minus that weight at the all-zero output string and minus that weight at every other output string. These real entries are included into the complex scalars.

Adjoin a reference in the computational basis state given by the constant string of pairs (0,0). The matrix unit at the pair of these two strings is positive semidefinite, since it is diagonal with nonnegative entries, and has trace one. Expansion of the tensor product with the identity shows that the amplified output is diagonal: it has the preceding channel-difference entries when the reference string is this fixed string, and zero entries at every other reference string.

The weights sum to one, by interchanging the sum over output strings with the product of the coordinate sums 1/4 + 3/4. The all-zero string has weight (1/4)^n, and every weight lies between zero and one. Consequently the absolute value of the difference entry at c is its weight plus 1 minus twice its weight if c is all zero, with no additional term otherwise. The trace norm of a real diagonal matrix is the sum of the absolute values of its entries. Summing first over the reference strings and then over c therefore gives exactly 2 times (1 minus (1/4)^n).

The chosen density matrix is one of the matrices in the supremum defining diamondNorm. Hence that norm is at least ENNReal.ofReal of 2 times (1 minus (1/4)^n). Passing this nonnegative expression into ENNReal gives the same expression there. Divide the bound by two and use the order reversal of subtraction from one. Since (1/4)^n is at most one, the two truncated subtractions cancel, yielding parallelError(n) at most (1/4)^n divided by two.

For n at least one, weaken this upper bound to (1/4)^n. Both n cast to the reals and Real.log 2 are positive. The ENNReal logarithm is monotone, and the logarithm of (1/4)^n is the real quantity minus 2 times n times Real.log 2, included into EReal. This follows from the real logarithm laws and Real.log 4 equal to twice Real.log 2. Negating the logarithmic inequality and multiplying by the nonnegative inverse normalization gives exponent(n) at least two, since the normalizing factors cancel.

Finally every sufficiently large natural n is at least one, so exponent is eventually at least two. If claim held, this inequality would pass to the limit in EReal and give two at most one, a contradiction. The argument excludes the limit one and supplies the stated lower bound; it does not determine the exact optimal asymptotic exponent.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.diamondNorm`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.exponent`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.harrowM`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.harrowMbar`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.parallelError`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.tensorPow`
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
