# The steering substitution need not preserve powers

## Abstract

An admissible five-dimensional projective family fails steering power preservation.

Fin d consists of the natural numbers below d, and Fin.val gives the natural representative. The function windowRoot d is exp(2πi/d), with the real and natural quantities included in the complex numbers. Complex.I is the imaginary unit, Complex.ofReal is the inclusion of the reals, and Nat.cast includes a natural number in the indicated scalar field. A star on a complex number means complex conjugation. Matrix multiplication and powers use the usual complex matrix algebra; a centered dot denotes scalar multiplication. Nat.div and Nat.mod are natural-number division and remainder, and subtraction between natural numbers is truncated at zero.

**Definition 1.1 (The phase coefficients).**

$$\forall (d: \mathbb{N}), (\forall (\phi: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\forall (n: \mathbb{N}), (\forall (y: \operatorname{Fin}\left(d\right)), (\forall (k: \operatorname{Fin}\left(d\right)), ((\operatorname{coeff}\left(d, \phi, n, y, k\right): \mathbb{C}) = ((\frac{(1: \mathbb{C})}{(\operatorname{Nat.cast}\left(d\right): \mathbb{C})}) \cdot ((\operatorname{windowRoot}\left(d\right))^{\operatorname{Nat.div}\left((((\operatorname{Fin.val}\left(k\right): \mathbb{N})) \cdot (n)) \cdot ((n) - (1)), 2\right)})) \cdot (\sum_{l: \operatorname{Fin}\left(d\right)} ((\operatorname{Complex.exp}\left((-\operatorname{Complex.I}) \cdot ((\operatorname{Complex.ofReal}\left((\sum_{(m: \mathbb{N}) \in \operatorname{Finset.range}\left(n\right)} (\phi\left((\langle \operatorname{Nat.mod}\left((((\operatorname{Fin.val}\left(l\right): \mathbb{N})) + (m)) + (1), d\right) \rangle: \operatorname{Fin}\left(d\right)), y\right)): \mathbb{R})\right): \mathbb{C}))\right)) \cdot ((\operatorname{windowRoot}\left(d\right))^{(((\operatorname{Fin.val}\left(k\right): \mathbb{N})) \cdot (n)) \cdot ((\operatorname{Fin.val}\left(l\right): \mathbb{N}))}))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.coeff` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Remigiusz Augusiak (2025). *Certifying classes of d-outcome measurements with quantum steering*. DOI: [10.1088/1367-2630/adda73](https://doi.org/10.1088/1367-2630/adda73). URL: <https://arxiv.org/abs/2410.20477v2>.

*Commentary.*

For real phases φ, coeff d φ n y k is the coefficient of the nth-power steering substitution. The inner sum uses m = 0, …, n − 1, so the phase index is l + m + 1 modulo d. The bound on l implies d > 0 whenever such an index is needed. Angle brackets designate the element of Fin d with the displayed natural representative. The real phase sum is included in ℂ before multiplication by −Complex.I. This is the coefficient in main2.tex, lines 204–206; the definition also allows every natural n and d.

**Definition 1.2 (Admissible phases).**

$$\forall (d: \mathbb{N}), (\forall (\phi: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), ((\operatorname{Admissible}\left(d, \phi\right)) \Leftrightarrow ((\forall (y: \operatorname{Fin}\left(d\right)), (\sum_{j: \operatorname{Fin}\left(d\right)} (\phi\left(j, y\right)) = (0: \mathbb{R}))) \land (\forall (n: \mathbb{N}), ((1 \le n) \Rightarrow ((n \le (d) - (1)) \Rightarrow (\forall (y: \operatorname{Fin}\left(d\right)), (\forall (y': \operatorname{Fin}\left(d\right)), (\sum_{k: \operatorname{Fin}\left(d\right)} ((\operatorname{star}\left(\operatorname{coeff}\left(d, \phi, n, y', k\right)\right)) \cdot (\operatorname{coeff}\left(d, \phi, n, y, k\right))) = \operatorname{ite}\left(y = y', (1: \mathbb{C}), (0: \mathbb{C})\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.Admissible` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Remigiusz Augusiak (2025). *Certifying classes of d-outcome measurements with quantum steering*. DOI: [10.1088/1367-2630/adda73](https://doi.org/10.1088/1367-2630/adda73). URL: <https://arxiv.org/abs/2410.20477v2>.

*Commentary.*

Each column of phases has real sum zero. For each natural n from 1 through d − 1, the coefficient rows indexed by y are orthonormal: the conjugated row is indexed by y′ and the unconjugated row by y. These are the zero-phase condition of main2.tex, lines 190–194 and 208–212, and the orthogonality condition of lines 234–236. At d = 0 or d = 1 there is no n in the specified interval.

**Definition 1.3 (Projective observables).**

$$\forall (d: \mathbb{N}), (\forall (B: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{IsProjectiveFamily}\left(d, B\right)) \Leftrightarrow (\forall (y: \operatorname{Fin}\left(d\right)), ((B\left(y\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land ((B\left(y\right))^{d} = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.IsProjectiveFamily` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Remigiusz Augusiak (2025). *Certifying classes of d-outcome measurements with quantum steering*. DOI: [10.1088/1367-2630/adda73](https://doi.org/10.1088/1367-2630/adda73). URL: <https://arxiv.org/abs/2410.20477v2>.

*Commentary.*

For each y, the complex d by d matrix B y is unitary and its dth power is the identity matrix. Thus its order divides d. This is the projective-observable condition of main2.tex, line 355, restricted to the Hilbert space ℂᵈ.

**Definition 1.4 (The steering substitution).**

$$\forall (d: \mathbb{N}), (\forall (\phi: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), (\forall (B: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (n: \mathbb{N}), (\forall (k: \operatorname{Fin}\left(d\right)), ((\operatorname{transformed}\left(d, \phi, B, n, k\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) = \sum_{y: \operatorname{Fin}\left(d\right)} ((\operatorname{coeff}\left(d, \phi, n, y, k\right)) \cdot ((B\left(y\right))^{n})))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.transformed` (`✓ std3`).

*Citation.* Alexandre C. Orthey; Remigiusz Augusiak (2025). *Certifying classes of d-outcome measurements with quantum steering*. DOI: [10.1088/1367-2630/adda73](https://doi.org/10.1088/1367-2630/adda73). URL: <https://arxiv.org/abs/2410.20477v2>.

*Commentary.*

The nth transformed operator at k is the sum of the nth powers of B y weighted by coeff d φ n y k. For projective observables these powers are the Fourier components indexed by n and y of the measurement. The definition is the substitution rule of main2.tex, lines 246–249, in the projective setting of line 355. It is defined for arbitrary B and phases, without assuming projectivity or admissibility.

**Definition 1.5 (Universal preservation of powers).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (d: \mathbb{N}), ((\operatorname{Nat.Prime}\left(d\right)) \Rightarrow (\forall (\phi: (\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R}))), ((\operatorname{Admissible}\left(d, \phi\right)) \Rightarrow (\forall (B: (\operatorname{Fin}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), ((\operatorname{IsProjectiveFamily}\left(d, B\right)) \Rightarrow (\forall (k: \operatorname{Fin}\left(d\right)), (\forall (n: \mathbb{N}), ((1 \le n) \Rightarrow ((n \le (d) - (1)) \Rightarrow (\operatorname{transformed}\left(d, \phi, B, n, k\right) = (\operatorname{transformed}\left(d, \phi, B, 1, k\right))^{n})))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Remigiusz Augusiak (2025). *Certifying classes of d-outcome measurements with quantum steering*. DOI: [10.1088/1367-2630/adda73](https://doi.org/10.1088/1367-2630/adda73). URL: <https://arxiv.org/abs/2410.20477v2>.

*Commentary.*

For every prime natural d, every admissible phase array and every projective family on ℂᵈ, the transformed operator at every k and every power n from 1 through d − 1 equals the nth power of the first transformed operator. This is the dimension-d matrix reading of Conjecture 1 in main2.tex, lines 1265–1273, under the projective assumption at line 1263. The conjecture permits Bob a larger Hilbert space; the displayed proposition only quantifies over d by d matrices. There is no hypothesis about a shared state or a measured violation of a steering inequality.

**Theorem 1.6 (A five-dimensional counterexample).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/orthey-augusiak-2025-steering-power-preservation-refutation` (refuted) by `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"orthey-augusiak-2025-steering-power-preservation-refutation","declaration_gid":"D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alexandre C. Orthey; Remigiusz Augusiak (2025). *Certifying classes of d-outcome measurements with quantum steering*. DOI: [10.1088/1367-2630/adda73](https://doi.org/10.1088/1367-2630/adda73). URL: <https://arxiv.org/abs/2410.20477v2>.

*Commentary.*

Take d = 5 and write ω = windowRoot 5. The primitive fifth root satisfies ω⁵ = 1, 1 + ω + ω² + ω³ + ω⁴ = 0 and star(ω) = ω⁴. For each y in Fin 5 choose the integer vector (−6(y.val : ℤ), 0, (y.val : ℤ) − 1, 1 + 2(y.val : ℤ), 3(y.val : ℤ)), include its coordinates in ℝ, and multiply them by 2π/5 to obtain φ(·,y). The five coordinates sum to zero. For every integer a, the exponential of −i(2π/5)(a : ℝ) is ω raised to the natural representative of (−a) modulo 5. Consequently all coefficient terms reduce to powers of ω with natural exponents modulo 5. For n = 1, 2, 3, 4 and all y,y′, expand the five-term sums, replace star(ω) by ω⁴, reduce exponents modulo 5 and replace ω⁴ by −1 − ω − ω² − ω³. The resulting polynomial identities give the required coefficient orthogonality, so these phases are admissible.

Use D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.shift and D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.clock. The matrix shift sends the coordinate vector at j to the vector at j + 1 modulo five; clock is diagonal with entry ω to the natural power j.val. For each y define Rᵧ as the sum over k in Fin 5 of star(coeff 5 φ 1 y k) times the matrix product of shift with clock^(k.val). The entries of shift are one exactly when the row i is j + 1, and zero otherwise. Expanding the coefficients in Rᵧ gives its (i,j) entry as zero unless i = j + 1; at that row it is ω^((aⱼ + y.val · j.val) mod 5), with a = (0,4,1,0,0).

Let U be the diagonal matrix with entries ω raised to the corresponding coordinates of (0,0,4,0,0). Each diagonal entry has modulus one, so U is unitary. The entry formula gives Rᵧ = U (shift clock^(y.val)) U*, using matrix multiplication and conjugate transpose. Both shift and clock are unitary, hence so is this product. To compute its fifth power, identify Fin 5 with ZMod 5 and apply the Weyl displacement power identity to the displacement with labels 1 and y. The natural numbers 5 and choose(5,2) = 10 both cast to zero in ZMod 5; the identity therefore gives fifth power one. Reindexing the matrices back to Fin 5 gives (shift clock^(y.val))⁵ = 1. Conjugation by U preserves powers, so Rᵧ⁵ = 1. Now take B₀ = ω R₀ and Bᵧ = Rᵧ for y ≠ 0. Multiplication by the scalar ω preserves unitarity and the fifth power, so B is a projective family.

At k = 0, expanding the same finite sums and matrix entries gives two reconstructions: the sum of coeff 5 φ 1 y 0 times Rᵧ is shift, and the sum of coeff 5 φ 2 y 0 times Rᵧ² is shift². Set g = (3 + ω + ω⁴)/5. Direct evaluation gives coeff 5 φ 1 0 0 = g and coeff 5 φ 2 0 0 = g. Only B₀ differs from R₀. Thus transformed 5 φ B 1 0 = shift + ((ω − 1)g) R₀, and transformed 5 φ B 2 0 = shift² + ((ω² − 1)g) R₀², where the products of complex coefficients with matrices are scalar multiplications. Expanding the square of the first matrix and using the entry formula for R₀ gives the (0,3) entry of (transformed 5 φ B 1 0)² − transformed 5 φ B 2 0 as g(g − 1)(ω − 1)².

Put s = ω + ω⁴. The fifth-root identities give s² + s = 1. If g = 0, then s = −3 and this equation reads 6 = 1; if g = 1, then s = 2 and it again reads 6 = 1. Hence g is neither zero nor one. Primitivity gives ω ≠ 1, so g(g − 1)(ω − 1)² is nonzero. If claim held, apply it to the prime 5, the admissible phases φ and the projective family B with k = 0 and n = 2. Since 1 ≤ 2 ≤ 4, it would identify transformed 5 φ B 2 0 with (transformed 5 φ B 1 0)², forcing this same (0,3) entry to vanish. This contradiction proves the negation of claim.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.Admissible`
- Truth anchor: `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.IsProjectiveFamily`
- Truth anchor: `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.coeff`
- Truth anchor: `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.transformed`
- Dependency: [D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation](../Information/StabilizerAutocorrelationNormRefutation.md)
