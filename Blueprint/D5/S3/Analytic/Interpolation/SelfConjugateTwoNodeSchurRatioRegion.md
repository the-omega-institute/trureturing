# Exact two-node regions for self-conjugate Schur-ratio and hook-Schur bounds

## Abstract

On two-node self-conjugate grids in the closed unit disk, both inequalities in Conjecture 6.2 of Ostrovskii and Shcherbakov collapse across all degrees t >= 2 to their first nontrivial degree t = 3. The shifted Schur-ratio bound holds precisely in a closed sector of opening 2*pi/3 with vertex -1, whose largest inscribed origin-centred disk has radius sqrt(3)/2; the nonnegative-real-part hook-Schur bound holds precisely in a closed hyperbolic region inside the right half-disk.

**Definition 1.1 (Two-variable complete homogeneous symmetric polynomial).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall m: \mathbb{N}, \forall x: R, \forall y: R, \operatorname{twoH}\left(m, x, y\right) = \sum_{i\in \operatorname{Finset.range}\left(m + 1\right)} x^{i} \cdot y^{m - i}$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.twoH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For any commutative ring R and natural degree m, twoH(m,x,y) sums x^i y^(m-i) over i in Finset.range(m+1), where i ranges over 0,...,m and natural subtraction is truncated at zero. Type denotes an arbitrary universe Type u.

**Definition 1.2 (Two-node complex conjugate pair).**

$$\forall a: \mathbb{R}, \forall b: \mathbb{R}, \operatorname{conjPair}\left(a, b\right) = ![\operatorname{ofReal}\left(a\right) + \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I}, \operatorname{ofReal}\left(a\right) - \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I}]$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.conjPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Given real coordinates a and b, conjPair(a,b) is the two-entry complex vector on Fin 2 taking value a + b*i at index 0 and a - b*i at index 1. ofReal embeds R into C, Complex.I is the imaginary unit, and ![u,v] denotes the Fin 2 vector literal.

**Definition 1.3 (Negated two-node complex conjugate pair).**

$$\forall a: \mathbb{R}, \forall b: \mathbb{R}, \operatorname{negConjPair}\left(a, b\right) = ![-(\operatorname{ofReal}\left(a\right) + \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I}), -(\operatorname{ofReal}\left(a\right) - \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I})]$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.negConjPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Given real coordinates a and b, negConjPair(a,b) is the two-entry complex vector on Fin 2 taking value -(a + b*i) at index 0 and -(a - b*i) at index 1, so that 1 - (negConjPair(a,b) + 1) equals conjPair(a,b) pointwise.

**Definition 1.4 (Real slack function for the shifted Schur ratio).**

$$\forall t: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, \operatorname{F}\left(t, a, b\right) = \operatorname{Nat.cast}\left(\mathbb{R}, t\right) \cdot (\operatorname{Nat.cast}\left(\mathbb{R}, t\right) - 1) \cdot (1 - a) - \operatorname{Nat.cast}\left(\mathbb{R}, t\right) + \operatorname{Re}\left(\operatorname{h}\left(t - 1, \operatorname{conjPair}\left(a, b\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For natural t and real a, b, F(t,a,b) is the real numerator slack t*(t-1)*(1-a) - t + Re(h(t-1, conjPair(a,b))). Natural subtraction t-1 is truncated at zero, Nat.cast embeds N into R, Re extracts the real part, and h is the complete homogeneous symmetric function on Fin 2 -> C.

**Definition 1.5 (Closed sector with vertex minus one).**

$$\forall z: (\operatorname{Fin}\left(2\right) \to \mathbb{C}), (\operatorname{inFirstSector}\left(z\right)) \Leftrightarrow (\forall i: \operatorname{Fin}\left(2\right), \left|\operatorname{Im}\left(z\left(i\right)\right)\right| \le \operatorname{Real.sqrt}\left(3\right) \cdot (\operatorname{Re}\left(z\left(i\right)\right) + 1))$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.inFirstSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

A two-node grid z : Fin 2 -> C lies in inFirstSector(z) when every entry satisfies |Im(z(i))| <= sqrt(3)*(Re(z(i)) + 1), cutting out the closed sector with vertex -1, axis [-1, infinity), and half-opening angle pi/3.

**Definition 1.6 (Real characteristic polynomial of a negated conjugate pair).**

$$\forall a: \mathbb{R}, \forall b: \mathbb{R}, \operatorname{charPolyNegConj}\left(a, b\right) = (\operatorname{Polynomial.X} + \operatorname{Polynomial.C}\left(a\right))^{2} + \operatorname{Polynomial.C}\left(b^{2}\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.charPolyNegConj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For real a and b, charPolyNegConj(a,b) is the monic quadratic real polynomial (X + C(a))^2 + C(b^2) in Polynomial(R), where Polynomial.X is the indeterminate and Polynomial.C embeds constants.

**Definition 1.7 (Real characteristic polynomial of a conjugate pair).**

$$\forall a: \mathbb{R}, \forall b: \mathbb{R}, \operatorname{charPolyConj}\left(a, b\right) = (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left(a\right))^{2} + \operatorname{Polynomial.C}\left(b^{2}\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.charPolyConj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For real a and b, charPolyConj(a,b) is the monic quadratic real polynomial (X - C(a))^2 + C(b^2) in Polynomial(R).

**Lemma 1.8 (Alternating binomial identity for twoH).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall t: \mathbb{N}, \forall x: R, \forall y: R, (2 \le t) \Rightarrow (\sum_{d\in \operatorname{Finset.range}\left(t - 1\right)} (-1)^{d} \cdot \operatorname{Nat.cast}\left(R, \operatorname{choose}\left(t, d + 2\right)\right) \cdot \operatorname{twoH}\left(d + 1, x, y\right) = \operatorname{Nat.cast}\left(R, t\right) - \operatorname{twoH}\left(t - 1, 1 - x, 1 - y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.alternating_choose_twoH_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Over any commutative ring R and for every integer t >= 2, the alternating sum over d in Finset.range(t-1) of (-1)^d * choose(t, d+2) * twoH(d+1, x, y) equals t - twoH(t-1, 1-x, 1-y). Induction on t >= 2 splits choose(t+1, d+2) by Pascal's identity and decomposes twoH(d+1, x, y) = x*twoH(d, x, y) + y^(d+1).

**Lemma 1.9 (Closed form of the two-node shifted Schur ratio).**

$$\forall t: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, (2 \le t) \Rightarrow ((a^{2} + b^{2} \le 1) \Rightarrow ((\operatorname{ofReal}\left(a\right) + \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I} \ne 1) \Rightarrow ((\operatorname{Q}\left(t, 2, 1, (\operatorname{negConjPair}\left(a, b\right) + 1)\right) = \frac{\operatorname{Nat.cast}\left(\mathbb{C}, t\right) - \operatorname{h}\left(t - 1, \operatorname{conjPair}\left(a, b\right)\right)}{\operatorname{Nat.cast}\left(\mathbb{C}, t\right) \cdot (\operatorname{Nat.cast}\left(\mathbb{C}, t\right) - 1) \cdot (1 - \operatorname{ofReal}\left(a\right))}) \land (\operatorname{Q}\left(2, 2, 1, (\operatorname{negConjPair}\left(a, b\right) + 1)\right) = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.Q_two_node_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For t >= 2 and w = a + b*i in the closed unit disk with w != 1, the two-node tableau hook Schur function schurHook(d,0,zeta) reduces to h(d+1,zeta) on zeta = negConjPair(a,b) + 1, while choose(t,2)*e(1,zeta) = t*(t-1)*(1-a) != 0. Applying alternating_choose_twoH_eq yields Q(t,2,1,negConjPair(a,b)+1) = (t - h(t-1,conjPair(a,b))) / (t*(t-1)*(1-a)), and in particular Q(2,2,1,negConjPair(a,b)+1) = 1.

**Lemma 1.10 (Equivalence between the ratio bound and nonnegativity of F).**

$$\forall t: \mathbb{N}, \forall a: \mathbb{R}, \forall b: \mathbb{R}, (2 \le t) \Rightarrow ((a^{2} + b^{2} \le 1) \Rightarrow ((\operatorname{ofReal}\left(a\right) + \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I} \ne 1) \Rightarrow ((\left\lVert \operatorname{Q}\left(t, 2, 1, (\operatorname{negConjPair}\left(a, b\right) + 1)\right) \right\rVert \le 1) \Leftrightarrow (0 \le \operatorname{F}\left(t, a, b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.first_inequality_iff_F_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

Because conjPair(a,b) is invariant under coordinate swap after complex conjugation, h(t-1,conjPair(a,b)) is real and bounded in absolute value by t on the closed unit disk, so t - h(t-1,conjPair(a,b)) >= 0 while t*(t-1)*(1-a) > 0 for w != 1. Consequently ||Q(t,2,1,negConjPair(a,b)+1)|| <= 1 holds if and only if 0 <= F(t,a,b).

**Theorem 1.11 (Exact sector region for the first two-node inequality).**

$$\forall a: \mathbb{R}, \forall b: \mathbb{R}, (a^{2} + b^{2} \le 1) \Rightarrow ((\operatorname{ofReal}\left(a\right) + \operatorname{ofReal}\left(b\right) \cdot \operatorname{Complex.I} \ne 1) \Rightarrow ((\operatorname{Polynomial.map}\left(\operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right), \operatorname{charPolyNegConj}\left(a, b\right)\right) = \prod_{i:\operatorname{Fin}\left(2\right)} (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left(\operatorname{negConjPair}\left(a, b\right)\left(i\right)\right))) \land (((\forall t: \mathbb{N}, (2 \le t) \Rightarrow (\left\lVert \operatorname{Q}\left(t, 2, 1, (\operatorname{negConjPair}\left(a, b\right) + 1)\right) \right\rVert \le 1)) \Leftrightarrow (\left\lVert \operatorname{Q}\left(3, 2, 1, (\operatorname{negConjPair}\left(a, b\right) + 1)\right) \right\rVert \le 1)) \land (((\left\lVert \operatorname{Q}\left(3, 2, 1, (\operatorname{negConjPair}\left(a, b\right) + 1)\right) \right\rVert \le 1) \Leftrightarrow (b^{2} \le 3 \cdot (1 - a)^{2})) \land (((b^{2} \le 3 \cdot (1 - a)^{2}) \Leftrightarrow (\operatorname{inFirstSector}\left(\operatorname{negConjPair}\left(a, b\right)\right))) \land ((b^{2} \le 3 \cdot (1 - a)^{2}) \Leftrightarrow (\operatorname{Polynomial.eval}\left(-1, \operatorname{charPolyNegConj}\left(a, b\right)\right) \le (\operatorname{Polynomial.eval}\left(-1, \operatorname{Polynomial.derivative}\left(\operatorname{charPolyNegConj}\left(a, b\right)\right)\right))^{2})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.first_inequality_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For w = a + b*i in the closed unit disk with w != 1, charPolyNegConj(a,b) factors over C as (X - z_0)*(X - z_1) for z = negConjPair(a,b). Moreover, ||Q(t,2,1,z+1)|| <= 1 holds for all t >= 2 if and only if it holds at t = 3, which is equivalent to b^2 <= 3*(1-a)^2, to inFirstSector(z), and to P(-1) <= P'(-1)^2 for P = charPolyNegConj(a,b). Uniform Lipschitz monotonicity of F(t,a,b) in a on the unit disk reduces the interior to the upper circular cap b^2 >= 3/4 and the sector boundary b = (sqrt(3)/2)*beta (0 < beta <= 1), where a cube-root-of-unity expansion and a large-t envelope establish F(t,a,b) >= 0 for all t >= 4.

**Theorem 1.12 (Largest origin-centred disk for the two-node Schur-ratio bound).**

$$\forall \rho: \mathbb{R}, (0 < \rho) \Rightarrow ((\rho \le 1) \Rightarrow ((\forall t: \mathbb{N}, \forall z: (\operatorname{Fin}\left(2\right) \to \mathbb{C}), (2 \le t) \Rightarrow ((\operatorname{selfConjugate}\left(z\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(2\right), \left\lVert z\left(i\right) \right\rVert \le \rho) \Rightarrow ((z \ne ![-1, -1]) \Rightarrow (\left\lVert \operatorname{Q}\left(t, 2, 1, (z + 1)\right) \right\rVert \le 1))))) \Leftrightarrow (\rho \le \frac{\operatorname{Real.sqrt}\left(3\right)}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.largest_admissible_disk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For 0 < rho <= 1, the universal bound ||Q(t,2,1,z+1)|| <= 1 holds for all t >= 2 and all two-node self-conjugate grids z != ![-1,-1] with ||z(i)|| <= rho if and only if rho <= sqrt(3)/2. Every two-node self-conjugate grid satisfies z(1) = conj(z(0)); when rho <= sqrt(3)/2, the sum-of-squares identity 3*(1-a)^2 - b^2 = (2*a - 3/2)^2 + (3/4 - (a^2 + b^2)) places z inside the admissible sector, whereas for rho > sqrt(3)/2 the boundary pair a = (sqrt(3)/2)*rho, b = rho/2 violates the t = 3 inequality.

**Theorem 1.13 (Exact hyperbolic region for the second two-node inequality).**

$$\forall a: \mathbb{R}, \forall b: \mathbb{R}, (0 \le a) \Rightarrow ((a^{2} + b^{2} \le 1) \Rightarrow ((\operatorname{Polynomial.map}\left(\operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right), \operatorname{charPolyConj}\left(a, b\right)\right) = \prod_{i:\operatorname{Fin}\left(2\right)} (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left(\operatorname{conjPair}\left(a, b\right)\left(i\right)\right))) \land ((\forall t: \mathbb{N}, (2 \le t) \Rightarrow ((\left\lVert \operatorname{schurHook}\left(t - 2, 0, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert \le \operatorname{Nat.cast}\left(\mathbb{R}, \operatorname{choose}\left(t, 2\right)\right) \cdot \left\lVert \operatorname{e}\left(1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert) \Leftrightarrow (\left\lVert \operatorname{h}\left(t - 1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert \le \operatorname{Nat.cast}\left(\mathbb{R}, t\right) \cdot (\operatorname{Nat.cast}\left(\mathbb{R}, t\right) - 1) \cdot a))) \land ((\left\lVert \operatorname{schurHook}\left(0, 0, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert = \operatorname{Nat.cast}\left(\mathbb{R}, \operatorname{choose}\left(2, 2\right)\right) \cdot \left\lVert \operatorname{e}\left(1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert) \land ((\left\lVert \operatorname{h}\left(1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert = 2 \cdot a) \land (((\forall t: \mathbb{N}, (2 \le t) \Rightarrow (\left\lVert \operatorname{schurHook}\left(t - 2, 0, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert \le \operatorname{Nat.cast}\left(\mathbb{R}, \operatorname{choose}\left(t, 2\right)\right) \cdot \left\lVert \operatorname{e}\left(1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert)) \Leftrightarrow (\left\lVert \operatorname{schurHook}\left(1, 0, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert \le \operatorname{Nat.cast}\left(\mathbb{R}, \operatorname{choose}\left(3, 2\right)\right) \cdot \left\lVert \operatorname{e}\left(1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert)) \land (((\left\lVert \operatorname{schurHook}\left(1, 0, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert \le \operatorname{Nat.cast}\left(\mathbb{R}, \operatorname{choose}\left(3, 2\right)\right) \cdot \left\lVert \operatorname{e}\left(1, \operatorname{conjPair}\left(a, b\right)\right) \right\rVert) \Leftrightarrow (b^{2} \le 3 \cdot a^{2} + 6 \cdot a)) \land ((b^{2} \le 3 \cdot a^{2} + 6 \cdot a) \Leftrightarrow (\operatorname{Polynomial.eval}\left(0, \operatorname{charPolyConj}\left(a, b\right)\right) \le (\operatorname{Polynomial.eval}\left(0, \operatorname{Polynomial.derivative}\left(\operatorname{charPolyConj}\left(a, b\right)\right)\right))^{2} - 3 \cdot \operatorname{Polynomial.eval}\left(0, \operatorname{Polynomial.derivative}\left(\operatorname{charPolyConj}\left(a, b\right)\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.second_inequality_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dmitrii M. Ostrovskii and Pavel S. Shcherbakov (2025). *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*. DOI: [10.48550/arXiv.2508.13554](https://doi.org/10.48550/arXiv.2508.13554). URL: <https://arxiv.org/abs/2508.13554v2>.

*Commentary.*

For w = a + b*i in the closed unit disk with a >= 0, charPolyConj(a,b) factors over C as (X - w_0)*(X - w_1) for w = conjPair(a,b). For every t >= 2, the hook-Schur bound ||schurHook(t-2,0,w)|| <= choose(t,2)*||e(1,w)|| is equivalent to ||h(t-1,w)|| <= t*(t-1)*a, with equality at t = 2 where ||h(1,w)|| = 2*a. Across all t >= 2, the family of inequalities is equivalent to its t = 3 instance, to b^2 <= 3*a^2 + 6*a, and to P(0) <= P'(0)^2 - 3*P'(0) for P = charPolyConj(a,b). Lipschitz transport in a reduces the region to the boundary hyperbola arc b^2 = 3*c^2 + 6*c (0 <= c <= 1/4), where explicit recurrence polynomials handle 3 <= t <= 7 and geometric norm decay handles t >= 8.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.F`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.Q_two_node_closed_form`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.alternating_choose_twoH_eq`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.charPolyConj`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.charPolyNegConj`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.conjPair`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.first_inequality_iff_F_nonneg`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.first_inequality_region`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.inFirstSector`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.largest_admissible_disk`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.negConjPair`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.second_inequality_region`
- Truth anchor: `D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion.twoH`
- Dependency: [D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation](SelfConjugateGridSchurRatioRefutation.md)
