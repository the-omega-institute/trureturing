# Integer Characters Determine Torus Orbit Closures

## Abstract

The closure of the nonnegative powers of any point of a finite torus is determined by exactly the integer characters that equal one at that point.

**Theorem 1.1 (The complete integer relation criterion).**

$$\forall I \in FiniteType,\; \forall g \in I \to Circle,\; \forall z \in I \to Circle,\; z \in \operatorname{closure}\left(\left\{g^{n} \mid n \in \mathbb{N}\right\}\right) \Leftrightarrow \left(\forall k \in I \to \mathbb{Z},\; \prod_{i\in I} \operatorname{g}\left(i\right)^{\operatorname{k}\left(i\right)} = 1 \Rightarrow \prod_{i\in I} \operatorname{z}\left(i\right)^{\operatorname{k}\left(i\right)} = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/TorusOrbitClosure.result` (`✓ std3`). ∎

*Citation.* A. L. Onishchik (2020). *Kronecker theorem*. URL: <https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528>.

*Commentary.*

This is the single-generator torus subgroup criterion in Kronecker's approximation theorem. Compactness identifies the closures of integer and nonnegative powers. The literature note gives the additive-to-multiplicative correspondence and the source locator.

Let I be any finite index type. Circle is the multiplicative group of complex numbers of modulus one, and powers of a function are taken coordinatewise. The closure uses the product topology. Natural powers include zero. Every integer vector k is tested, including negative exponents, and the implication retains exactly the relations of g.

The nonnegative power orbit has the same closure as the integer power orbit. This closure is a compact subgroup G. Continuity of each character proves that its value is one throughout G whenever its value at g is one.

For the converse, average continuous functions over G using normalized Haar measure, and compare this average with the average over zG. Translation by g forces the integral of a character to vanish unless the character equals one at g. For the remaining characters, the assumed relation makes translation by z leave the integral unchanged. The dense span of the torus characters therefore makes the two continuous linear averaging functionals equal on every continuous complex-valued function. If z were outside G, the compact cosets G and zG would be disjoint. A continuous function equal to zero on G and one on zG would then have both equal and unequal averages, a contradiction.

No independence or algebraicity condition is imposed on the phases. The empty index type, finite periodic orbits, and proper closed subgroups are included. In one coordinate g = -1 retains the even integer relation lattice and the two-point subgroup. The statement asserts a topological characterization, with no algorithm for finding a finite generating family of integer relations.

## References

- Truth anchor: `D5/S3/Fourier/TorusOrbitClosure.result`
