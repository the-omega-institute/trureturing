# Inverse squared chord circulants

## Abstract

Fourier analysis of inverse squared chord weights gives the alternating block-product spectrum.

**Definition 1.1 (The interaction weights).**

$$\forall (m: \mathbb{N}), (\forall (j: \operatorname{Fin}\left((2) \cdot (m)\right)), (\forall (k: \operatorname{Fin}\left((2) \cdot (m)\right)), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.weights}\left(m, j, k\right) = \operatorname{ite}\left(j = k, (0: \mathbb{R}), \frac{(1: \mathbb{R})}{(4) \cdot ((\operatorname{Real.sin}\left(\frac{(\operatorname{Real.pi}) \cdot (((\operatorname{Fin.val}\left(j\right): \mathbb{R})) - ((\operatorname{Fin.val}\left(k\right): \mathbb{R})))}{(2) \cdot ((m: \mathbb{R}))}\right))^{2})}\right))))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Off the diagonal the weight is the reciprocal squared distance between unit vertices of a regular 2m-gon. The diagonal is zero. These weights are constructed from the polygon interactions of Barry–Kevrekidis, Section 4.1 (arXiv:1306.1545v2, TeX lines 552–577).

**Definition 1.2 (The alternating sign matrix).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.chargeMatrix}\left(m\right) = \operatorname{Nat.casesOn}\left(m, (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(0\right), \operatorname{Fin}\left(0\right), \mathbb{R}\right)), \lambda (n: \mathbb{N}) \mapsto (\operatorname{D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse.indexParity}\left(((2) \cdot (n)) + (1), 2\right))\right))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.chargeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The zero-size matrix is zero. At a successor m=n+1, indexParity (2n+1) 2 constructs the diagonal alternating-sign matrix. The next identity identifies its entries without a case distinction.

**Theorem 1.3 (The diagonal charge identity).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.chargeMatrix}\left(m\right) = \operatorname{Matrix.diagonal}\left(\lambda (j: \operatorname{Fin}\left((2) \cdot (m)\right)) \mapsto ((-((1: \mathbb{R})))^{(\operatorname{Fin.val}\left(j\right)) + (2)})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.chargeMatrix_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The charge matrix is diagonal with jth entry (−1)^(j.val+2). For m=0 there is no index; for m=n+1 the identity follows from the diagonal definition of indexParity and commutativity of natural addition.

**Definition 1.4 (The alternating Fourier value).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.diagonalWeight}\left(m\right) = (\frac{(((((2) \cdot (m): \mathbb{N}): \mathbb{R}))^{2}) - (1)}{12}) - (\frac{((m: \mathbb{R}))^{2}}{2}))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.diagonalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

For m≥3, this scalar is the half-period Fourier value of the inverse-squared-chord weights. The product 2m is first formed in the natural numbers and then cast to the reals; m is also cast before squaring.

**Definition 1.5 (The upper-right block).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.blockB}\left(m\right) = (((\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.diagonalWeight}\left(m\right)) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left((2) \cdot (m)\right), \operatorname{Fin}\left((2) \cdot (m)\right), \mathbb{R}\right)))) - (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.weights}\left(m\right))) \cdot (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.chargeMatrix}\left(m\right)))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.blockB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Subtract the interaction matrix from diagonalWeight times the identity, then multiply on the right by the charge matrix.

**Definition 1.6 (The lower-left block).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.blockC}\left(m\right) = ((((\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.diagonalWeight}\left(m\right)) + ((1: \mathbb{R}))) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left((2) \cdot (m)\right), \operatorname{Fin}\left((2) \cdot (m)\right), \mathbb{R}\right)))) - (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.weights}\left(m\right))) \cdot (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.chargeMatrix}\left(m\right)))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.blockC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The second block has the same form with diagonalWeight increased by one before scalar multiplication.

**Theorem 1.7 (The signed row sum).**

$$\forall (m: \mathbb{N}), ((3 \le m) \Rightarrow (\forall (j: \operatorname{Fin}\left((2) \cdot (m)\right)), (\sum_{k: \operatorname{Fin}\left((2) \cdot (m)\right)} (((-((1: \mathbb{R})))^{(\operatorname{Fin.val}\left(k\right)) + (2)}) \cdot (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.weights}\left(m, j, k\right))) = ((-((1: \mathbb{R})))^{(\operatorname{Fin.val}\left(j\right)) + (2)}) \cdot (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.diagonalWeight}\left(m\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.alternating_weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

For m≥3, the charge-weighted sum along row j equals the jth charge times diagonalWeight m. Translate the cyclic difference j−k to the summation index. Alternating signs are the half-period character, so the sum is the Fourier coefficient in mode m. Evaluating that coefficient yields the scalar.

**Definition 1.8 (The paired mode value).**

$$\forall (m: \mathbb{N}), (\forall (k: \operatorname{ZMod}\left((2) \cdot (m)\right)), (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.gamma}\left(m, k\right) = \operatorname{let} (r: \mathbb{N}) = \operatorname{min}\left(\operatorname{ZMod.val}\left(k\right), (((2) \cdot (m)) - (\operatorname{ZMod.val}\left(k\right)): \mathbb{N})\right) \operatorname{in} \frac{((((m: \mathbb{R})) - ((r: \mathbb{R})))^{2}) \cdot ((((r: \mathbb{R}))^{2}) - (2))}{4}))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

For positive m, the minimum of the two natural distances is the folded cyclic distance r of the residue k from zero. The formula is defined for every natural m. Cast m and r to real numbers before computing (m−r)²(r²−2)/4. The subtraction 2m−k.val inside the minimum remains natural subtraction.

**Theorem 1.9 (The block-product determinant).**

$$\forall (m: \mathbb{N}), ([\operatorname{NeZero}\left((2) \cdot (m)\right)] (3 \le m) \Rightarrow (\forall (y: \mathbb{R}), (\operatorname{Matrix.det}\left(((y) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left((2) \cdot (m)\right), \operatorname{Fin}\left((2) \cdot (m)\right), \mathbb{R}\right)))) - ((\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.blockC}\left(m\right)) \cdot (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.blockB}\left(m\right)))\right) = \prod_{k: \operatorname{ZMod}\left((2) \cdot (m)\right)} ((y) - (\operatorname{D5.S3.FluidDynamics.Vortices.InverseChordCirculant.gamma}\left(m, k\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.product_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Reindex the matrices by ZMod (2m) and include their real entries in the complex numbers. The weight matrix is circulant. Conjugating it by the diagonal charge matrix multiplies its cyclic kernel by alternating signs, while the square of the charge matrix is the identity. Thus blockC times blockB becomes the product of two circulants, with scalar identity terms diagonalWeight+1 and diagonalWeight. The common Fourier matrix has nonzero determinant and diagonalizes both circulants; taking determinants gives the product of their mode factors. The inverse-squared-chord Fourier value at mode k is ((2m)²−1)/12−k.val(2m−k.val)/2. To obtain it, the quadratic mode function has periodic second difference 1−2m at zero and 1 elsewhere, and its sum is zero by the finite sums of first and second powers. Fourier transformation of that difference equation multiplies by −4sin²(πl.val/(2m)); division at nonzero l and the zero-sum identity at l=0 identify the kernel. Fourier inversion then gives all its Fourier values. Alternating signs shift mode k to k+m. Multiplying the two resulting real factors, separating k.val<m from k.val≥m, gives gamma m (k+m). Finally, translating the product index by m and using injectivity of the real inclusion proves the stated real determinant identity.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.alternating_weight_sum`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.blockB`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.blockC`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.chargeMatrix`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.chargeMatrix_diagonal`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.diagonalWeight`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.gamma`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.product_spectrum`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/InverseChordCirculant.weights`
- Dependency: [D5/S3/ArithUnits/MercaCosetFiberLift](../../ArithUnits/MercaCosetFiberLift.md)
- Dependency: [D5/S3/Fourier/SparseGeneratorFamily](../../Fourier/SparseGeneratorFamily.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/SaturatedActualHistories](../../ObserverMemory/Algorithms/SaturatedActualHistories.md)
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse](../../Quantum/Algebra/ZeitlinSixJ/Inverse.md)
- Dependency: [D5/S3/Quantum/Matrix/CirculantCharpoly](../../Quantum/Matrix/CirculantCharpoly.md)
