# WeightedGapPolynomialCertificate

## Abstract

Weighted Dirichlet eigenvalues and a fixed affine spectral gap comparison.

**Definition 1.1 (interval).**

$$interval = (Icc 0 Real . pi)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.interval` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The closed interval from zero to Real.pi is the spatial domain.

**Definition 1.2 (boundedMeasurable).**

$$\forall (f: \mathbb{R} \to \mathbb{R}), boundedMeasurable f = (Measurable (fun x : interval \mapsto f x) \land \exists B : \mathbb{R} , \forall x : \mathbb{R} , x \in interval \to | f x | \leq B)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.boundedMeasurable` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The restriction to the interval is measurable and has a uniform absolute-value bound.

**Definition 1.3 (potentialClass).**

$$\forall (M: WithTop \mathbb{R}), \forall (V: \mathbb{R} \to \mathbb{R}), potentialClass M V = (boundedMeasurable V \land ConvexOn \mathbb{R} interval V \land \forall x : \mathbb{R} , x \in interval \to 0 \leq V x \land (V x : WithTop \mathbb{R}) \leq M)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.potentialClass` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Definition 3.1, page 4: “For 1<M ≤ ∞ and 0 < N_{<,>} < ∞, let” “𝒞_M={V(x): 0≤V(x)≤M : V(x) is convex on [0,π]}.” Bounded measurability is the standing hypothesis in Section 2, page 2. M belongs to WithTop Real.

**Definition 1.4 (weightClass).**

$$\forall (Nlo Nhi: \mathbb{R}), \forall (w: \mathbb{R} \to \mathbb{R}), weightClass Nlo Nhi w = (boundedMeasurable w \land ConcaveOn \mathbb{R} interval w \land \forall x : \mathbb{R} , x \in interval \to Nlo \leq w x \land w x \leq Nhi)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.weightClass` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Definition 3.1, page 4: “𝒮_{N_{<,>}}={w(x): N_<≤w(x)≤N_>: w(x) is concave on [0,π]}.” Nlo and Nhi denote the finite real bounds N_< and N_>. Bounded measurability is the standing hypothesis in Section 2, page 2.

**Definition 1.5 (dirichletTrial).**

$$\forall (u: \mathbb{R} \to \mathbb{R}), dirichletTrial u = (ContDiffOn \mathbb{R} 1 u interval \land \forall x : \mathbb{R} , x \neg \in Ioo 0 Real . pi \to u x = 0)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.dirichletTrial` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Trial functions are continuously differentiable on the closed interval and vanish outside its interior.

**Definition 1.6 (energy).**

$$\forall (V u: \mathbb{R} \to \mathbb{R}), energy V u = (\int_{(0 : \mathbb{R})}^{Real . pi} ((derivWithin u interval x) ^{2} + V x \cdot (u x) ^{2}) d x)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.energy` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The Dirichlet quadratic form integrates the squared derivative plus the potential times the squared function.

**Definition 1.7 (weightedMass).**

$$\forall (w u: \mathbb{R} \to \mathbb{R}), weightedMass w u = (\int_{(0 : \mathbb{R})}^{Real . pi} (w x \cdot (u x) ^{2}) d x)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.weightedMass` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The weighted quadratic form integrates the weight times the squared function.

**Definition 1.8 (minmaxUpperBounds).**

$$\forall (V w: \mathbb{R} \to \mathbb{R}), \forall (n: \mathbb{N}), minmaxUpperBounds V w n = (\{ r | \exists L : Submodule \mathbb{R} (\mathbb{R} \to \mathbb{R}) , FiniteDimensional \mathbb{R} L \land Module . finrank \mathbb{R} L = n \land (\forall u : \mathbb{R} \to \mathbb{R} , u \in L \to dirichletTrial u) \land (\forall u : \mathbb{R} \to \mathbb{R} , u \in L \to energy V u \leq r \cdot weightedMass w u) \})$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.minmaxUpperBounds` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

These are the upper bounds of the Rayleigh quotient on some trial subspace of the specified dimension, written after multiplying by the weighted mass.

**Definition 1.9 (isSpectrum).**

$$\forall (V w: \mathbb{R} \to \mathbb{R}), \forall (e: \mathbb{N} \to \mathbb{R}), isSpectrum V w e = ((\forall n : \mathbb{N} , 0 < e n) \land StrictMono e \land (\forall R : \mathbb{R} , \exists N : \mathbb{N} , \forall n : \mathbb{N} , N \leq n \to R < e n) \land \forall n : \mathbb{N} , (minmaxUpperBounds V w (n + 1)) . Nonempty \land BddBelow (minmaxUpperBounds V w (n + 1)) \land IsGLB (minmaxUpperBounds V w (n + 1)) (e n))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.isSpectrum` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The positive strictly increasing sequence diverges to infinity, and its entries are greatest lower bounds of the nonempty, bounded-below min-max upper-bound sets.

**Definition 1.10 (isShootingEigenvalue).**

$$\forall (V w: \mathbb{R} \to \mathbb{R}), \forall (z: \mathbb{R}), isShootingEigenvalue V w z = (\exists u : \mathbb{R} \to \mathbb{R} , ContinuousOn u interval \land IntervalIntegrable (fun t : \mathbb{R} \mapsto (V t - z \cdot w t) \cdot u t) volume 0 Real . pi \land u 0 = 0 \land u Real . pi = 0 \land \forall x : \mathbb{R} , x \in interval \to u x = x + \int_{(0 : \mathbb{R})}^{x} ((x - t) \cdot (V t - z \cdot w t) \cdot u t) d t)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.isShootingEigenvalue` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

A shooting eigenvalue admits a continuous solution of the integrated equation with initial slope one and zero values at both endpoints.

**Definition 1.11 (gap).**

$$\forall (e: \mathbb{N} \to \mathbb{R}), gap e = (e 1 - e 0)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.gap` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The fundamental gap is the second entry minus the first entry of the spectrum.

**Definition 1.12 (claim).**

$$claim = (\forall (M : WithTop \mathbb{R}) (Nlo Nhi : \mathbb{R}) (V w : \mathbb{R} \to \mathbb{R}) , (1 : WithTop \mathbb{R}) < M \to 0 < Nlo \to 0 < Nhi \to potentialClass M V \to weightClass Nlo Nhi w \to ((\exists e : \mathbb{N} \to \mathbb{R} , isSpectrum V w e) \land (\exists e0 : \mathbb{N} \to \mathbb{R} , isSpectrum (Function . const \mathbb{R} 0) w e0)) \land (\forall (e e0 : \mathbb{N} \to \mathbb{R}) , isSpectrum V w e \to isSpectrum (Function . const \mathbb{R} 0) w e0 \to gap e0 \leq gap e))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.claim` (`✓ std3`).

*Citation.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Open Problem 3.3, page 10: “Let w be a positive concave weight on [0,π]. Does the constant potential minimzer the fundamental spectral gap over the class of convex potentials. Equivalently,” “Γ[V,w]≥Γ[0,w]” “for every convex potential V.” The index zero is λ₁ and index one is λ₂. Both spectra are asserted to exist; the comparison quantifies over their min-max values.

**Definition 1.13 (State).**

$$structure State where ; prev : \mathbb{R} ; cur : \mathbb{R} ; next : \mathbb{R} ; total : \mathbb{R}$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The four real coordinates store the two lagged coefficients, the next coefficient, and the accumulated series sum.

**Definition 1.14 (state).**

$$\forall (A B: \mathbb{R}), state A B = (fun (n : \mathbb{N}) \mapsto match n with | 0 \mapsto \langle 0 , 0 , 1 , 1 \rangle | n + 1 \mapsto let s : = state A B n ; let c : = (A \cdot s . cur + B \cdot s . prev) / ((n + 1 : \mathbb{R}) \cdot (n + 2 : \mathbb{R})) ; \langle s . cur , s . next , c , s . total + c \rangle)$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.state` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The recurrence advances the coefficient coordinates and adds the newly computed coefficient to the accumulated sum.

**Definition 1.15 (Certificate).**

$$structure Certificate where ; a : (\mathbb{Q} \times \mathbb{Q}) ; b : (\mathbb{Q} \times \mathbb{Q}) ; coeff : \mathbb{N} \to (\mathbb{Q} \times \mathbb{Q}) ; total : \mathbb{N} \to (\mathbb{Q} \times \mathbb{Q}) ; ac : \mathbb{N} \to (\mathbb{Q} \times \mathbb{Q}) ; bp : \mathbb{N} \to (\mathbb{Q} \times \mathbb{Q}) ; add : \mathbb{N} \to (\mathbb{Q} \times \mathbb{Q})$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Rational pairs enclose the two parameters, coefficients, accumulated sums, products, and additions.

**Definition 1.16 (inputBox).**

$$\forall (d: Certificate), \forall (n: \mathbb{N}), inputBox d n = (! [ d . a , d . b , d . coeff (n - 1) , d . coeff n , d . total n ])$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.inputBox` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The five rational intervals enclose the two parameters, the lagged coefficient, the current coefficient, and the accumulated sum.

**Definition 1.17 (coeffExpr).**

$$\forall (d: Certificate), \forall (n: \mathbb{N}), coeffExpr d n = (Expr . mul (d . coeff (n + 2)) . 1 (d . coeff (n + 2)) . 2 (Expr . add (d . add n) . 1 (d . add n) . 2 (Expr . mul (d . ac n) . 1 (d . ac n) . 2 (Expr . input 0 d . a . 1 d . a . 2) (Expr . input 3 (d . coeff n) . 1 (d . coeff n) . 2)) (Expr . mul (d . bp n) . 1 (d . bp n) . 2 (Expr . input 1 d . b . 1 d . b . 2) (Expr . input 2 (d . coeff (n - 1)) . 1 (d . coeff (n - 1)) . 2))) (Expr . const (1 / ((n + 1 : \mathbb{Q}) \cdot (n + 2 : \mathbb{Q}))) (1 / ((n + 1 : \mathbb{Q}) \cdot (n + 2 : \mathbb{Q}))) (1 / ((n + 1 : \mathbb{Q}) \cdot (n + 2 : \mathbb{Q})))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.coeffExpr` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The rational expression computes the next coefficient from the two parameters and the lagged coefficients.

**Definition 1.18 (totalExpr).**

$$\forall (d: Certificate), \forall (n: \mathbb{N}), totalExpr d n = (Expr . add (d . total (n + 1)) . 1 (d . total (n + 1)) . 2 (Expr . input 4 (d . total n) . 1 (d . total n) . 2) (coeffExpr d n))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.totalExpr` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The rational expression adds the next coefficient to the accumulated sum.

**Definition 1.19 (stepCheck).**

$$\forall (d: Certificate), \forall (n: \mathbb{N}), stepCheck d n = (Bool . and (check (inputBox d n) (coeffExpr d n)) (check (inputBox d n) (totalExpr d n)))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.stepCheck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Both rational-expression checks must return true for a step to pass.

**Definition 1.20 (StateEnclosed).**

$$\forall (d: Certificate), \forall (n: \mathbb{N}), \forall (s: State), StateEnclosed d n s = ((s . prev \in Set . Icc (((d . coeff (n - 1))) . 1 : \mathbb{R}) (((d . coeff (n - 1))) . 2 : \mathbb{R})) \land (s . cur \in Set . Icc (((d . coeff n)) . 1 : \mathbb{R}) (((d . coeff n)) . 2 : \mathbb{R})) \land (s . next \in Set . Icc (((d . coeff (n + 1))) . 1 : \mathbb{R}) (((d . coeff (n + 1))) . 2 : \mathbb{R})) \land (s . total \in Set . Icc (((d . total n)) . 1 : \mathbb{R}) (((d . total n)) . 2 : \mathbb{R})))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.StateEnclosed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Each of the four state coordinates belongs to its indicated rational interval.

**Theorem 1.21 (checked_state).**

$$\forall (d: Certificate), \forall (A B: \mathbb{R}), ((A \in Set . Icc ((d . a) . 1 : \mathbb{R}) ((d . a) . 2 : \mathbb{R}))) \Rightarrow (((B \in Set . Icc ((d . b) . 1 : \mathbb{R}) ((d . b) . 2 : \mathbb{R}))) \Rightarrow ((StateEnclosed d 0 (state A B 0)) \Rightarrow (\forall (N: \mathbb{N}), (\forall n : \mathbb{N} , n < N \to stepCheck d n = true) \Rightarrow (StateEnclosed d N (state A B N)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.checked_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The initial enclosures and successful checks at every preceding step imply the enclosures after the specified number of recurrence steps.

**Definition 1.22 (piBox0).**

$$piBox0 = (((157079632679489661923 / 50000000000000000000) , (314159265358979323847 / 100000000000000000000)))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.piBox0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The displayed rational pair encloses Real.pi.

**Definition 1.23 (aValue0).**

$$aValue0 = (value ! [ Real . pi ] (Expr . mul (- 2428617296895856086949561 / 250000000000000000000000) (- 303577162111982010866747 / 31250000000000000000000) (Expr . mul (- 1973899782799512047386383 / 200000000000000000000000) (- 9869498913997560236869083 / 1000000000000000000000000) (Expr . neg (- 999989311923 / 1000000000000) (- 999989311923 / 1000000000000) (Expr . const (999989311923 / 1000000000000) (999989311923 / 1000000000000) (999989311923 / 1000000000000))) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)))) (Expr . add (19685840734641020676153 / 20000000000000000000000) (9842920367320510338077 / 10000000000000000000000) (Expr . const 1 1 1) (Expr . neg (- 314159265358979323847 / 20000000000000000000000) (- 157079632679489661923 / 10000000000000000000000) (Expr . mul (157079632679489661923 / 10000000000000000000000) (314159265358979323847 / 20000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . const (1 / 200) (1 / 200) (1 / 200)))))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.aValue0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Definition 1.24 (bValue0).**

$$bValue0 = (value ! [ Real . pi ] (Expr . mul (- 310059452828271778268331 / 1000000000000000000000000) (- 310059452828271778265369 / 1000000000000000000000000) (Expr . mul (31006276680299820175398047 / 1000000000000000000000000) (3875784585037477521961767 / 125000000000000000000000) (Expr . mul (4934802200544679309408941 / 500000000000000000000000) (4934802200544679309440357 / 500000000000000000000000) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000)) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . input 0 (157079632679489661923 / 50000000000000000000) (314159265358979323847 / 100000000000000000000))) (Expr . const (- 999989311923 / 100000000000000) (- 999989311923 / 100000000000000) (- 999989311923 / 100000000000000))))$$

*Formalization.* `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.bValue0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The scalar is the value of the displayed rational expression at Real.pi.

**Theorem 1.25 (pi_enclosed0).**

$$(Real . pi \in Set . Icc ((piBox0) . 1 : \mathbb{R}) ((piBox0) . 2 : \mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.pi_enclosed0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Real.pi belongs to the rational interval with the displayed endpoints.

**Theorem 1.26 (polynomial_sign0).**

$$(1 : \mathbb{R}) / 10 ^{15} < (state aValue0 bValue0 79) . total$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.polynomial_sign0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The accumulated polynomial value has the displayed strict signed margin.

**Theorem 1.27 (aValue_eq0).**

$$aValue0 = - (Real . pi ^{2}) \cdot ((999989311923 / 1000000000000) : \mathbb{R}) \cdot (1 - Real . pi / 200)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.aValue_eq0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.28 (bValue_eq0).**

$$bValue0 = Real . pi ^{3} \cdot ((0 : \mathbb{R}) - ((999989311923 / 1000000000000) : \mathbb{R})) / 100$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.bValue_eq0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

Evaluation of the rational expression gives the displayed rescaled shooting coefficient.

**Theorem 1.29 (a_bound0).**

$$| aValue0 | \leq 64$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.a_bound0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

**Theorem 1.30 (b_bound0).**

$$| bValue0 | \leq 32$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.b_bound0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohammed Ahrami (2026). *On the fundamental spectral gap of weighted Schrodinger operators*. DOI: [10.48550/arXiv.2605.24560](https://doi.org/10.48550/arXiv.2605.24560). URL: <https://arxiv.org/abs/2605.24560v1>.

*Commentary.*

The absolute value of the evaluated coefficient satisfies the displayed numerical bound.

## References

- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.Certificate`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.State`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.StateEnclosed`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.aValue0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.aValue_eq0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.a_bound0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.bValue0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.bValue_eq0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.b_bound0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.boundedMeasurable`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.checked_state`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.claim`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.coeffExpr`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.dirichletTrial`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.energy`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.gap`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.inputBox`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.interval`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.isShootingEigenvalue`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.isSpectrum`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.minmaxUpperBounds`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.piBox0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.pi_enclosed0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.polynomial_sign0`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.potentialClass`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.state`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.stepCheck`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.totalExpr`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.weightClass`
- Truth anchor: `D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.weightedMass`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
