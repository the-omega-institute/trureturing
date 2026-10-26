# A qudit counterexample to genuine entropic tetrahedra

## Abstract

The eight-level four-party pure state has an admissible zero-volume fill but is not biseparable, refuting the qudit genuine-entanglement claim.

**Definition 1.1 (One-party reduced density matrix).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (a: \operatorname{Fin}\left(d\right)), (\forall (a': \operatorname{Fin}\left(d\right)), (\operatorname{rho1}\left(\psi, i, a, a'\right) = \sum_{x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{ite}\left(x\left(i\right) = a, (\psi\left(x\right)) \cdot (\operatorname{star}\left(\psi\left(\operatorname{Function.update}\left(x, i, a'\right)\right)\right)), (0: \mathbb{C})\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.rho1` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

For a four-party coefficient function ψ, rho1 ψ i is the reduced density matrix of party i in the computational basis. Its (a,a') entry sums ψ(x) times the conjugate of the coefficient obtained by replacing the i-th coordinate of x by a', over all basis labels x whose i-th coordinate equals a.

**Definition 1.2 (Two-party reduced density matrix).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\forall (a: (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))), (\forall (a': (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))), (\operatorname{rho2}\left(\psi, i, j, a, a'\right) = \sum_{x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{ite}\left((x\left(i\right) = \operatorname{Prod.fst}\left(a\right)) \land (x\left(j\right) = \operatorname{Prod.snd}\left(a\right)), (\psi\left(x\right)) \cdot (\operatorname{star}\left(\psi\left(\operatorname{Function.update}\left(\operatorname{Function.update}\left(x, i, \operatorname{Prod.fst}\left(a'\right)\right), j, \operatorname{Prod.snd}\left(a'\right)\right)\right)\right)), (0: \mathbb{C})\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.rho2` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

For distinct party indices i and j, rho2 ψ i j is the two-party reduced density matrix. The entry indexed by (a,a') sums the coefficient product over labels whose i and j coordinates are the two components of a, replacing those coordinates by the components of a'.

**Definition 1.3 (Base-two spectral entropy).**

$$\forall (n: Type), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall (\rho: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), (\operatorname{entropy2}\left(\rho\right) = \frac{\operatorname{entropy}\left(\rho\right)}{\operatorname{Real.log}\left((2: \mathbb{R})\right)}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.entropy2` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

entropy2 divides the repository's natural-log spectral entropy by the natural logarithm of the real number 2, giving the base-two von Neumann entropy used by the source (TeX lines 65 and 107).

**Definition 1.4 (Biseparability across a proper cut).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), (\operatorname{Biseparable}\left(\psi\right) = \exists (X: \operatorname{Finset}\left(\operatorname{Fin}\left(4\right)\right)), ((\operatorname{Finset.Nonempty}\left(X\right)) \land ((\operatorname{Finset.Nonempty}\left(\operatorname{Compl.compl}\left(X\right)\right)) \land (\exists (\varphi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), (\exists (chi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), ((\forall (x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)), (\forall (y: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)), ((\forall (i: \operatorname{Fin}\left(4\right)), ((i \in X) \Rightarrow (x\left(i\right) = y\left(i\right)))) \Rightarrow (\varphi\left(x\right) = \varphi\left(y\right))))) \land ((\forall (x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)), (\forall (y: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)), ((\forall (i: \operatorname{Fin}\left(4\right)), ((\neg (i \in X)) \Rightarrow (x\left(i\right) = y\left(i\right)))) \Rightarrow (chi\left(x\right) = chi\left(y\right))))) \land (\forall (x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)), (\psi\left(x\right) = (\varphi\left(x\right)) \cdot (chi\left(x\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.Biseparable` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

Biseparable ψ holds when a nonempty proper finite set X of parties admits factors φ and χ, with φ depending only on coordinates in X, χ depending only on coordinates outside X, and ψ equal to their pointwise product.

**Definition 1.5 (Admissible entropic fill).**

$$\forall (d: \mathbb{N}), (\forall (\psi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), (\forall (\sigma: \operatorname{Fin}\left(6\right) \to \mathbb{R}), (\forall (ell: \mathbb{R}), (\operatorname{AdmissibleFill}\left(\psi, \sigma, ell\right) = \left((\forall (k: \operatorname{Fin}\left(6\right)), ((0: \mathbb{R}) \le \sigma\left(k\right))) \land ((((\sigma\left((0: \operatorname{Fin}\left(6\right))\right)) + (\sigma\left((1: \operatorname{Fin}\left(6\right))\right))) + (\sigma\left((2: \operatorname{Fin}\left(6\right))\right)) = \operatorname{entropy2}\left(\operatorname{rho1}\left(\psi, (0: \operatorname{Fin}\left(4\right))\right)\right)) \land ((((\sigma\left((0: \operatorname{Fin}\left(6\right))\right)) + (\sigma\left((3: \operatorname{Fin}\left(6\right))\right))) + (\sigma\left((4: \operatorname{Fin}\left(6\right))\right)) = \operatorname{entropy2}\left(\operatorname{rho1}\left(\psi, (1: \operatorname{Fin}\left(4\right))\right)\right)) \land ((((\sigma\left((1: \operatorname{Fin}\left(6\right))\right)) + (\sigma\left((3: \operatorname{Fin}\left(6\right))\right))) + (\sigma\left((5: \operatorname{Fin}\left(6\right))\right)) = \operatorname{entropy2}\left(\operatorname{rho1}\left(\psi, (2: \operatorname{Fin}\left(4\right))\right)\right)) \land ((((\sigma\left((2: \operatorname{Fin}\left(6\right))\right)) + (\sigma\left((4: \operatorname{Fin}\left(6\right))\right))) + (\sigma\left((5: \operatorname{Fin}\left(6\right))\right)) = \operatorname{entropy2}\left(\operatorname{rho1}\left(\psi, (3: \operatorname{Fin}\left(4\right))\right)\right)) \land ((((-(\operatorname{Real.sqrt}\left((\sigma\left((0: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((5: \operatorname{Fin}\left(6\right))\right))\right))) + (\operatorname{Real.sqrt}\left((\sigma\left((1: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((4: \operatorname{Fin}\left(6\right))\right))\right))) + (\operatorname{Real.sqrt}\left((\sigma\left((2: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((3: \operatorname{Fin}\left(6\right))\right))\right)) = (ell) \cdot (\operatorname{entropy2}\left(\operatorname{rho2}\left(\psi, (0: \operatorname{Fin}\left(4\right)), (1: \operatorname{Fin}\left(4\right))\right)\right))) \land ((((\operatorname{Real.sqrt}\left((\sigma\left((0: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((5: \operatorname{Fin}\left(6\right))\right))\right)) + (-(\operatorname{Real.sqrt}\left((\sigma\left((1: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((4: \operatorname{Fin}\left(6\right))\right))\right)))) + (\operatorname{Real.sqrt}\left((\sigma\left((2: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((3: \operatorname{Fin}\left(6\right))\right))\right)) = (ell) \cdot (\operatorname{entropy2}\left(\operatorname{rho2}\left(\psi, (0: \operatorname{Fin}\left(4\right)), (2: \operatorname{Fin}\left(4\right))\right)\right))) \land (((\operatorname{Real.sqrt}\left((\sigma\left((0: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((5: \operatorname{Fin}\left(6\right))\right))\right)) + (\operatorname{Real.sqrt}\left((\sigma\left((1: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((4: \operatorname{Fin}\left(6\right))\right))\right))) + (-(\operatorname{Real.sqrt}\left((\sigma\left((2: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((3: \operatorname{Fin}\left(6\right))\right))\right))) = (ell) \cdot (\operatorname{entropy2}\left(\operatorname{rho2}\left(\psi, (0: \operatorname{Fin}\left(4\right)), (3: \operatorname{Fin}\left(4\right))\right)\right)))))))))\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.AdmissibleFill` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

An admissible fill consists of six nonnegative real coordinates and a real parameter ell. The four sums of three coordinates equal the four one-party entropies, and the three signed radical sums equal ell times the two-party entropies. The coordinate order is AB, AC, AD, BC, BD, CD, as in the source's face and radical equations (TeX lines 103–121).

**Definition 1.6 (Entropic tetrahedron volume).**

$$\forall (\sigma: \operatorname{Fin}\left(6\right) \to \mathbb{R}), (\operatorname{volume}\left(\sigma\right) = \operatorname{let} p = \operatorname{Real.sqrt}\left((\sigma\left((0: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((5: \operatorname{Fin}\left(6\right))\right))\right); \operatorname{let} q = \operatorname{Real.sqrt}\left((\sigma\left((1: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((4: \operatorname{Fin}\left(6\right))\right))\right); \operatorname{let} r = \operatorname{Real.sqrt}\left((\sigma\left((2: \operatorname{Fin}\left(6\right))\right)) \cdot (\sigma\left((3: \operatorname{Fin}\left(6\right))\right))\right); ((\frac{\operatorname{Real.sqrt}\left((2: \mathbb{R})\right)}{(3: \mathbb{R})}) \cdot (\operatorname{Real.sqrt}\left(((2: \mathbb{R})) \cdot (\sum_{k: \operatorname{Fin}\left(6\right)} (\sigma\left(k\right)))\right))) \cdot (\operatorname{Real.rpow}\left((((((p) + (q)) + (r)) \cdot (((-(p)) + (q)) + (r))) \cdot (((p) + (-(q))) + (r))) \cdot (((p) + (q)) + (-(r))), \frac{(1: \mathbb{R})}{(4: \mathbb{R})}\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.volume` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

The volume uses p, q and r for the square roots of the products of opposite coordinate pairs. It is sqrt(2)/3 times the square root of twice the total coordinate sum, multiplied by the one-fourth real power of the four Heron-type factors. This is the source volume formula (TeX lines 91–101).

**Definition 1.7 (The qudit genuine-entanglement claim).**

$$\operatorname{claim} = (\forall (d: \mathbb{N}), (((2: \mathbb{N}) \le d) \Rightarrow (\forall (\psi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), ((\sum_{x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)} ((\left\lVert \psi\left(x\right) \right\rVert)^{(2: \mathbb{N})}) = (1: \mathbb{R})) \Rightarrow ((\exists (\sigma: \operatorname{Fin}\left(6\right) \to \mathbb{R}), (\exists (ell: \mathbb{R}), (\operatorname{AdmissibleFill}\left(\psi, \sigma, ell\right)))) \Rightarrow ((\forall (\sigma: \operatorname{Fin}\left(6\right) \to \mathbb{R}), (\forall (ell: \mathbb{R}), ((\operatorname{AdmissibleFill}\left(\psi, \sigma, ell\right)) \Rightarrow (\operatorname{volume}\left(\sigma\right) = (0: \mathbb{R}))))) \Rightarrow (\operatorname{Biseparable}\left(\psi\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.claim` (`✓ std3`).

*Citation.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

For every natural d at least 2 and every unit four-party state ψ, if an admissible fill exists and every admissible fill has zero volume, then ψ is biseparable. This is the formal version of the source's scalability conjecture that the tetrahedron measure is a genuine four-qudit measure (TeX lines 218–220).

**Theorem 1.8 (The qudit claim is false).**

$$\neg (\forall (d: \mathbb{N}), (((2: \mathbb{N}) \le d) \Rightarrow (\forall (\psi: \left(\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C}), ((\sum_{x: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(d\right)} ((\left\lVert \psi\left(x\right) \right\rVert)^{(2: \mathbb{N})}) = (1: \mathbb{R})) \Rightarrow ((\exists (\sigma: \operatorname{Fin}\left(6\right) \to \mathbb{R}), (\exists (ell: \mathbb{R}), (\operatorname{AdmissibleFill}\left(\psi, \sigma, ell\right)))) \Rightarrow ((\forall (\sigma: \operatorname{Fin}\left(6\right) \to \mathbb{R}), (\forall (ell: \mathbb{R}), ((\operatorname{AdmissibleFill}\left(\psi, \sigma, ell\right)) \Rightarrow (\operatorname{volume}\left(\sigma\right) = (0: \mathbb{R}))))) \Rightarrow (\operatorname{Biseparable}\left(\psi\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/xie-younis-mei-eberly-2024-qudit-tetrahedron-genuine-refutation` (refuted) by `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"xie-younis-mei-eberly-2024-qudit-tetrahedron-genuine-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Songbo Xie; Daniel Younis; Yuhan Mei; Joseph H. Eberly (2024). *Multipartite Entanglement: A Journey Through Geometry*. DOI: [10.3390/e26030217](https://doi.org/10.3390/e26030217). URL: <https://arxiv.org/abs/2304.03281v2>.

*Commentary.*

Use the eight-level state supported on the labels (4b+2c+d,b,c,d), with b, c and d in {0,1}, and amplitude 1/sqrt(8) on each supported label. The support-label bijection has eight terms, so the squared norm sum is one.

Summing the reduced-matrix entries gives the identity matrix divided by 8 for party A and a diagonal matrix with two entries 1/2 and six entries zero for each of B, C and D. The base-two entropies are therefore 3, 1, 1 and 1.

Subtract the A face equation from the sum of the other three face equations. Nonnegativity forces the BC, BD and CD coordinates to vanish, and the face equations then force AB, AC and AD to equal 1. The tuple (1,1,1,0,0,0) with ell equal to zero satisfies all three radical equations, so an admissible fill exists. Every radical factor in the volume is zero, hence the volume is zero.

If the state factored across a nonempty proper cut, the resulting product-minor identity would hold for every pair of basis labels. Applying it to the three pairs formed from the zero label and the labels 4, 2 and 1, then checking the membership choices for all four parties, contradicts the support equations for every proper cut. Thus the state is not biseparable.

Applying the claimed implication at d equal to 8 to this normalized state, its admissible fill and its zero-volume property would give biseparability, contradicting the preceding minor argument. Therefore the full claim is false.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.AdmissibleFill`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.Biseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.entropy2`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.rho1`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.rho2`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.volume`
- Dependency: [D5/S3/Quantum/Entanglement/FourMUBBoundEntanglementRefutation](../FourMUBBoundEntanglementRefutation.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](../../Information/ChenKatoBrandaoCMIRefutation.md)
