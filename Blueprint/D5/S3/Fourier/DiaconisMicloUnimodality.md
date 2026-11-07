# A counterexample to Diaconis–Miclo absolute-gap unimodality

## Abstract

The absolute spectral gap of a four-speed walk on ZMod 11 has a strict three-point valley.

**Definition 1.1 (Interpolated speed transfer).**

$$\forall G \in Type,\;  [AddGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; \forall a \in \mathbb{R},\; \forall v \in \{v: G // v \in S\},\; \forall w \in \{v: G // v \in S\},\; K\left(S, a, v, w\right) = ite\left(v = w, \left(1 - a\right) \cdot \frac{1}{(\operatorname{Finset}.\operatorname{card}\left(S\right): \mathbb{R})} + a, \left(1 - a\right) \cdot \frac{1}{(\operatorname{Finset}.\operatorname{card}\left(S\right): \mathbb{R})}\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.K` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Equation (1.9), p. 578: “∀ a ∈ [0,1],  K⁽ᵃ⁾ := (1 − a)K⁽⁰⁾ + aK⁽¹⁾”. Here K⁽⁰⁾ is uniform on S and K⁽¹⁾ is the identity. Speed values are elements of the subtype {v : G // v ∈ S}.

**Definition 1.2 (Position–speed transition).**

$$\forall G \in Type,\;  [AddGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; \forall a \in \mathbb{R},\; \forall p \in G \times \{v: G // v \in S\},\; \forall q \in G \times \{v: G // v \in S\},\; positionSpeed\left(S, a, p, q\right) = ite\left(q.1 = p.1 + p.2.1, K\left(S, a, p.2, q.2\right), 0\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.positionSpeed` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Equation (1.6), p. 577: “P((x,y),(x′,y′)) = δ_xy(x′) K_{x′}(y,y′)”. In additive notation the next position is x+v and the new speed is sampled from K.

**Definition 1.3 (The first-order walk).**

$$\forall G \in Type,\;  [AddGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; \forall x \in G,\; \forall y \in G,\; randomWalk\left(S, x, y\right) = ite\left(y - x \in S, \frac{1}{(\operatorname{Finset}.\operatorname{card}\left(S\right): \mathbb{R})}, 0\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.randomWalk` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Equation (1.8), p. 578: “L(x,x′) = μ(x′ − x)”. The measure μ is uniform on the symmetric generating set S.

**Definition 1.4 (Stationary-mean-zero functions).**

$$\forall alpha \in Type,\; [Fintype\left(alpha\right)] , \forall w \in alpha \to \mathbb{R},\; \forall f \in alpha \to \mathbb{C},\; meanZero\left(w, f\right) = \left(\sum_{x: alpha} ((w\left(x\right): \mathbb{C}) \cdot f\left(x\right)) = 0\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.meanZero` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Page 575: “By invariance of m, the subspace F_*(m,ℂ) := {F ∈ F(V²,ℂ) : m[F] = 0} is stable under M, so let Θ_*(M) ⊂ ℂ be the spectrum of M_*, the restriction of M to F_*(m,ℂ).” Finite weighted expectation is a sum; real weights are coerced to ℂ.

**Definition 1.5 (Eigenvalues on mean-zero functions).**

$$\forall alpha \in Type,\; [Fintype\left(alpha\right)] , \forall A \in Matrix\left(alpha, alpha, \mathbb{R}\right),\; \forall w \in alpha \to \mathbb{R},\; eigenvaluesMeanZero\left(A, w\right) = \{theta: \mathbb{C} \mid \exists f \in alpha \to \mathbb{C},\; (\exists x \in alpha,\; f\left(x\right) \ne 0)\land (meanZero\left(w, f\right))\land (\forall i \in alpha,\; \sum_{j: alpha} ((A\left(i, j\right): \mathbb{C}) \cdot f\left(j\right)) = theta \cdot f\left(i\right))\}$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.eigenvaluesMeanZero` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Page 575: “By invariance of m, the subspace F_*(m,ℂ) := {F ∈ F(V²,ℂ) : m[F] = 0} is stable under M, so let Θ_*(M) ⊂ ℂ be the spectrum of M_*, the restriction of M to F_*(m,ℂ).” The finite-dimensional expression asks for a nonzero complex eigenfunction of stationary mean zero.

**Definition 1.6 (Absolute spectral radius).**

$$\forall alpha \in Type,\; [Fintype\left(alpha\right)] , \forall A \in Matrix\left(alpha, alpha, \mathbb{R}\right),\; \forall w \in alpha \to \mathbb{R},\; spectralRadiusOnMeanZero\left(A, w\right) = sSup\left(\operatorname{Set}.\operatorname{image}\left((\lambda (theta: \mathbb{C}) \mapsto \left\lVert theta \right\rVert), eigenvaluesMeanZero\left(A, w\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.spectralRadiusOnMeanZero` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Page 575: “The spectral gap of M is λ(M) := 1 − max{|θ| : θ ∈ Θ_*(M)} ∈ [0,1]”. The finite nonempty eigenvalue set in this example permits the maximum's expression as sSup of the norm image.

**Definition 1.7 (Absolute spectral gap).**

$$\forall alpha \in Type,\; [Fintype\left(alpha\right)] , \forall A \in Matrix\left(alpha, alpha, \mathbb{R}\right),\; \forall w \in alpha \to \mathbb{R},\; spectralGapOnMeanZero\left(A, w\right) = 1 - spectralRadiusOnMeanZero\left(A, w\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.spectralGapOnMeanZero` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Page 575: “The spectral gap of M is λ(M) := 1 − max{|θ| : θ ∈ Θ_*(M)} ∈ [0,1]”. The maximum concerns modulus, including negative and nonreal eigenvalues.

**Definition 1.8 (The interpolated second-order gap).**

$$\forall G \in Type,\; [Fintype\left(G\right)] [AddGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; \forall a \in \mathbb{R},\; lambdaM\left(S, a\right) = 1 - sSup\left(\left\{\left\lVert theta \right\rVert \mid theta \in \{theta: \mathbb{C} \mid \exists f \in G \times \{v: G // v \in S\} \to \mathbb{C},\; (\exists p \in G \times \{v: G // v \in S\},\; f\left(p\right) \ne 0)\land (\sum_{p: G \times \{v: G // v \in S\}} ((\frac{1}{(\operatorname{Fintype}.\operatorname{card}\left(G\right) \cdot \operatorname{Finset}.\operatorname{card}\left(S\right): \mathbb{R})}: \mathbb{C}) \cdot f\left(p\right)) = 0)\land (\forall p \in G \times \{v: G // v \in S\},\; \sum_{q: G \times \{v: G // v \in S\}} ((positionSpeed\left(S, a, p, q\right): \mathbb{C}) \cdot f\left(q\right)) = theta \cdot f\left(p\right))\}\right\}\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.lambdaM` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Equation (1.10), p. 578: “∀ x,x′ ∈ G,  m(x,x′) := 1/(|G| |S|)” if x′ − x ∈ S, and “0” otherwise. The gap is computed on G × {v : G // v ∈ S}, with the uniform weights and the position–speed matrix. The displayed expression expands the gap and its mean-zero eigenvalue set. A finite instance on this subtype is supplied by Fintype.ofFinite.

**Definition 1.9 (The underlying first-order gap).**

$$\forall G \in Type,\; [Fintype\left(G\right)] [AddGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; lambdaL\left(S\right) = 1 - sSup\left(\left\{\left\lVert theta \right\rVert \mid theta \in \{theta: \mathbb{C} \mid \exists f \in G \to \mathbb{C},\; (\exists x \in G,\; f\left(x\right) \ne 0)\land (\sum_{x: G} ((\frac{1}{(\operatorname{Fintype}.\operatorname{card}\left(G\right): \mathbb{R})}: \mathbb{C}) \cdot f\left(x\right)) = 0)\land (\forall x \in G,\; \sum_{y: G} ((randomWalk\left(S, x, y\right): \mathbb{C}) \cdot f\left(y\right)) = theta \cdot f\left(x\right))\}\right\}\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.lambdaL` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Page 576: “Similar definitions can be given for the spectral gap of L, by replacing the state space V² by V.” The underlying first-order walk uses weight 1/|G| on G and the same absolute spectral gap.

**Definition 1.10 (Conjecture 1.3).**

$$claim = \left(\forall G \in Type,\; [Fintype\left(G\right)] [AddCommGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; 2 \le \operatorname{Finset}.\operatorname{card}\left(S\right) \Rightarrow \left(\left(\forall v \in G,\; v \in S \Rightarrow -v \in S\right) \Rightarrow \left(\operatorname{AddSubgroup}.\operatorname{closure}\left((S: Set\left(G\right))\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists a0 \in \mathbb{R},\; (0 \le a0)\land (a0 \le 1)\land (MonotoneOn\left((\lambda (a: \mathbb{R}) \mapsto lambdaM\left(S, a\right)), \operatorname{Set}.\operatorname{Icc}\left(0, a0\right)\right))\land (AntitoneOn\left((\lambda (a: \mathbb{R}) \mapsto lambdaM\left(S, a\right)), \operatorname{Set}.\operatorname{Icc}\left(a0, 1\right)\right))\land (\exists c1 \in \mathbb{R},\; \exists c2 \in \mathbb{R},\; (0 < c1)\land (c1 < c2)\land (c1 \cdot \operatorname{Real}.\operatorname{sqrt}\left(lambdaL\left(S\right)\right) \le lambdaM\left(S, a0\right))\land (lambdaM\left(S, a0\right) \le c2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(lambdaL\left(S\right)\right)))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/DiaconisMicloUnimodality.claim` (`✓ std3`).

*Citation.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

Conjecture 1.3, p. 580, verbatim: “Let G be a finite Abelian group and S be a generating set of G with |S| ≥ 2. Let K⁽¹⁾ be the identity S × S matrix (seen as a speed transfer kernel, it forces the chain to keep going always in the same direction) and consider again the interpolating kernels given in (1.9), as well as the associated second order Markov kernels M⁽ᵃ⁾ for a ∈ [0,1], which are also trajectorially reversible with respect to the probability measure m defined in (1.10). There exists a₀ ∈ [0,1] such that λ(M⁽ᵃ⁾) is nondecreasing for a ∈ [0,a₀] and nonincreasing on [a₀,1]. Furthermore there exists two values 0 < c₁ < c₂ (perhaps depending on |S|), such that c₁ √λ(L) ≤ λ(M⁽ᵃ⁰⁾) ≤ c₂ √λ(L).” The additive finite group G and symmetric generating finset S carry the stated construction. Both clauses use the same turning point. The claim quantifies G : Type at universe zero, which contains ZMod 11, and the result is its closed negation.

**Theorem 1.11 (The conjecture is false).**

$$\neg (\forall G \in Type,\; [Fintype\left(G\right)] [AddCommGroup\left(G\right)] , \forall S \in Finset\left(G\right),\; 2 \le \operatorname{Finset}.\operatorname{card}\left(S\right) \Rightarrow \left(\left(\forall v \in G,\; v \in S \Rightarrow -v \in S\right) \Rightarrow \left(\operatorname{AddSubgroup}.\operatorname{closure}\left((S: Set\left(G\right))\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists a0 \in \mathbb{R},\; (0 \le a0)\land (a0 \le 1)\land (MonotoneOn\left((\lambda (a: \mathbb{R}) \mapsto lambdaM\left(S, a\right)), \operatorname{Set}.\operatorname{Icc}\left(0, a0\right)\right))\land (AntitoneOn\left((\lambda (a: \mathbb{R}) \mapsto lambdaM\left(S, a\right)), \operatorname{Set}.\operatorname{Icc}\left(a0, 1\right)\right))\land (\exists c1 \in \mathbb{R},\; \exists c2 \in \mathbb{R},\; (0 < c1)\land (c1 < c2)\land (c1 \cdot \operatorname{Real}.\operatorname{sqrt}\left(lambdaL\left(S\right)\right) \le lambdaM\left(S, a0\right))\land (lambdaM\left(S, a0\right) \le c2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(lambdaL\left(S\right)\right)))\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DiaconisMicloUnimodality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Persi Diaconis; Laurent Miclo (2013). *On the spectral analysis of second-order Markov chains*. DOI: [10.5802/afst.1383](https://doi.org/10.5802/afst.1383). URL: <https://hal.science/hal-00719047v1>.

*Commentary.*

For G=ZMod 11 and S={1,2,9,10}={±1,±2}, the gap is greater than 261/500 at a=1/5 and a=3/10, and less than 261/500 at a=1/4. No monotone-then-antitone function has this strict valley. Fourier reduction gives four-dimensional character blocks; exact Schur inequalities bound their endpoint roots by 239/500. A middle-parameter real root has larger modulus. This refutes the conjunction through its unimodality clause. The square-root comparison considered separately and product-group extensions remain open.

## References

- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.K`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.claim`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.eigenvaluesMeanZero`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.lambdaL`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.lambdaM`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.meanZero`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.positionSpeed`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.randomWalk`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.result`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.spectralGapOnMeanZero`
- Truth anchor: `D5/S3/Fourier/DiaconisMicloUnimodality.spectralRadiusOnMeanZero`
- Dependency: [D5/S3/Arith/Congruence/RestrictedSpineConstantPotential](../Arith/Congruence/RestrictedSpineConstantPotential.md)
- Dependency: [D5/S3/Fourier/FullBispectrumStability](FullBispectrumStability.md)
