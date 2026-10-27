# Derivative cancellation and hinge majorization

## Abstract

Derivative cancellation gives a common convex minimum and two monotone rays.

**Definition 1.1 (hingeIntegral).**

$$\forall h : (\mathbb{R} \to \mathbb{R}), (\forall k : (\mathbb{R} \to \mathbb{R}), (\forall T : \mathbb{R}, (\forall c : \mathbb{R}, (\operatorname{hingeIntegral}\left(h, k, T, c\right) = (\int_{s:\mathbb{R} \in \operatorname{Set}.\operatorname{Ioi}\left(0\right)} (\operatorname{max}\left((\operatorname{abs}\left((h\left(s\right)) + ((c) \cdot (k\left(s\right)))\right)) - (T), 0\right)))))))$$

*Formalization.* `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.hingeIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

The integral of the nonnegative part of the thresholded absolute value along the affine family h+c*k. All set integrals use real Lebesgue measure.

**Theorem 1.2 (radial).**

$$\forall g : (\mathbb{R} \to \mathbb{R}), (\int_{r:\mathbb{R}\times\mathbb{R}} (g\left(((\operatorname{Prod}.\operatorname{fst}\left(r\right))^{2}) + ((\operatorname{Prod}.\operatorname{snd}\left(r\right))^{2})\right)) = ((\operatorname{Real}.\operatorname{pi}) \cdot (\int_{s:\mathbb{R} \in \operatorname{Set}.\operatorname{Ioi}\left(0\right)} (g\left(s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.radial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

The squared-radius substitution reduces a planar radial Bochner integral to pi times its integral on the positive half-line. This identity also respects the zero value assigned to nonintegrable Bochner integrals.

**Theorem 1.3 (boundary_cancellation).**

$$\forall h : (\mathbb{R} \to \mathbb{R}), (\forall k : (\mathbb{R} \to \mathbb{R}), ((\operatorname{Continuous}\left(h\right)) \Rightarrow ((\forall x : \mathbb{R}, (\operatorname{HasDerivAt}\left(h, k\left(x\right), x\right))) \Rightarrow ((\operatorname{MeasureTheory}.\operatorname{IntegrableOn}\left(k, \operatorname{Set}.\operatorname{Ioi}\left(0\right)\right)) \Rightarrow (\forall p : \mathbb{R}, ((0 \le p) \Rightarrow ((\forall x : \mathbb{R}, ((x \in \operatorname{Set}.\operatorname{Ioo}\left(0, p\right)) \Rightarrow (0 \le k\left(x\right)))) \Rightarrow ((\forall x : \mathbb{R}, ((x \in \operatorname{Set}.\operatorname{Ioi}\left(p\right)) \Rightarrow (k\left(x\right) \le 0))) \Rightarrow ((h\left(0\right) = (0)) \Rightarrow ((\operatorname{Filter}.\operatorname{Tendsto}\left(h, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)) \Rightarrow (\forall T : \mathbb{R}, (\int_{s:\mathbb{R} \in \operatorname{Set}.\operatorname{Ioi}\left(0\right)} ((k\left(s\right)) \cdot (\operatorname{ite}\left(T < h\left(s\right), 1, 0\right))) = (0)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.boundary_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

A differentiable function that starts and ends at zero and has a nonnegative derivative before p and a nonpositive derivative after p has zero derivative integral over every strict superlevel set. Substitution on the two monotone intervals cancels their common endpoint. The remaining endpoint integral tends to zero.

**Theorem 1.4 (hinge_min).**

$$\forall h : (\mathbb{R} \to \mathbb{R}), (\forall k : (\mathbb{R} \to \mathbb{R}), ((\operatorname{Continuous}\left(h\right)) \Rightarrow ((\operatorname{Continuous}\left(k\right)) \Rightarrow ((\operatorname{MeasureTheory}.\operatorname{IntegrableOn}\left(h, \operatorname{Set}.\operatorname{Ioi}\left(0\right)\right)) \Rightarrow ((\operatorname{MeasureTheory}.\operatorname{IntegrableOn}\left(k, \operatorname{Set}.\operatorname{Ioi}\left(0\right)\right)) \Rightarrow ((\forall s : \mathbb{R}, ((s \in \operatorname{Set}.\operatorname{Ioi}\left(0\right)) \Rightarrow (0 \le h\left(s\right)))) \Rightarrow (\forall T : \mathbb{R}, (\forall c : \mathbb{R}, ((0 \le T) \Rightarrow ((\int_{s:\mathbb{R} \in \operatorname{Set}.\operatorname{Ioi}\left(0\right)} ((k\left(s\right)) \cdot (\operatorname{ite}\left(T < h\left(s\right), 1, 0\right))) = (0)) \Rightarrow (\operatorname{hingeIntegral}\left(h, k, T, 0\right) \le \operatorname{hingeIntegral}\left(h, k, T, c\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.hinge_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

If h is nonnegative on the positive half-line and the derivative-direction superlevel integral vanishes, the thresholded absolute-value integral is minimized at coefficient zero. A pointwise subgradient inequality gives the integral comparison.

**Theorem 1.5 (hinge_convex).**

$$\forall h : (\mathbb{R} \to \mathbb{R}), (\forall k : (\mathbb{R} \to \mathbb{R}), ((\operatorname{Continuous}\left(h\right)) \Rightarrow ((\operatorname{Continuous}\left(k\right)) \Rightarrow ((\operatorname{MeasureTheory}.\operatorname{IntegrableOn}\left(h, \operatorname{Set}.\operatorname{Ioi}\left(0\right)\right)) \Rightarrow ((\operatorname{MeasureTheory}.\operatorname{IntegrableOn}\left(k, \operatorname{Set}.\operatorname{Ioi}\left(0\right)\right)) \Rightarrow (\forall T : \mathbb{R}, ((0 \le T) \Rightarrow (\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Set}.\operatorname{univ}, \operatorname{hingeIntegral}\left(h, k, T\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.hinge_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

For a nonnegative threshold, the integral is a finite convex function of the affine coefficient. The triangle inequality bounds its values at convex combinations.

**Theorem 1.6 (convex_rays).**

$$\forall F : (\mathbb{R} \to \mathbb{R}), ((\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Set}.\operatorname{univ}, F\right)) \Rightarrow ((\forall c : \mathbb{R}, (F\left(0\right) \le F\left(c\right))) \Rightarrow ((\operatorname{MonotoneOn}\left(F, \operatorname{Set}.\operatorname{Ici}\left(0\right)\right)) \land (\operatorname{AntitoneOn}\left(F, \operatorname{Set}.\operatorname{Iic}\left(0\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.convex_rays` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni (2025). *Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states*. DOI: [10.1103/w561-h3z5](https://doi.org/10.1103/w561-h3z5). URL: <https://arxiv.org/abs/2412.19698v3>.

*Commentary.*

A real convex function with a global minimum at zero is monotone on the nonnegative ray and antitone on the nonpositive ray.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.boundary_cancellation`
- Truth anchor: `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.convex_rays`
- Truth anchor: `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.hingeIntegral`
- Truth anchor: `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.hinge_convex`
- Truth anchor: `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.hinge_min`
- Truth anchor: `D5/S3/Analytic/Convexity/DerivativeHingeMajorization.radial`
