# Miña-Díaz–Rubin Equipotential Refutation

## Abstract

A degree-one monic Faber polynomial is Chebyshev on a compact set but fails on an exterior equipotential.

**Definition 1.1 (Monic sup-norm minimization).**

$$\forall E: \operatorname{Set}\left(\mathbb{C}\right), \forall n: \mathbb{N}, \forall p: \operatorname{Polynomial}\left(\mathbb{C}\right), \operatorname{IsChebyshev}\left(E, n, p\right) \Leftrightarrow ((\operatorname{Monic}\left(p\right)) \land ((\operatorname{natDegree}\left(p\right) = n) \land (\forall q: \operatorname{Polynomial}\left(\mathbb{C}\right), (\operatorname{Monic}\left(q\right)) \Rightarrow ((\operatorname{natDegree}\left(q\right) = n) \Rightarrow (\forall M: \mathbb{R}, (\forall z: \mathbb{C}, (z \in E) \Rightarrow (\Vert \operatorname{eval}\left(q, z\right)\Vert \le M)) \Rightarrow (\forall z: \mathbb{C}, (z \in E) \Rightarrow (\Vert \operatorname{eval}\left(p, z\right)\Vert \le M)))))))$$

*Formalization.* `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.IsChebyshev` (`✓ std3`).

*Citation.* Erwin Miña-Díaz; Olof Rubin (2025). *Chebyshev polynomials on equipotential curves*. URL: <https://arxiv.org/abs/2505.03967v1>.

*Commentary.*

A monic polynomial p of degree n is Chebyshev on E if every uniform real bound for any monic degree-n competitor q also bounds p on E. On a compact nonempty set this is sup-norm minimization. The definition uses pointwise bounds rather than a supremum operator.

**Definition 1.2 (The monic Faber normalization).**

$$\forall \psi: \mathbb{C}\to \mathbb{C}, \forall \kappa: \mathbb{R}, \forall n: \mathbb{N}, \forall F: \operatorname{Polynomial}\left(\mathbb{C}\right), \operatorname{IsMonicFaber}\left(\psi, \kappa, n, F\right) \Leftrightarrow ((\operatorname{Monic}\left(F\right)) \land ((\operatorname{natDegree}\left(F\right) = n) \land (\operatorname{Tendsto}\left((w: \mathbb{C} \mapsto \operatorname{eval}\left(F, \psi\left(w\right)\right) - \left((\kappa: \mathbb{C}) \cdot w\right)^{n}), \operatorname{cobounded}\left(\mathbb{C}\right), \operatorname{nhds}\left(0\right)\right))))$$

*Formalization.* `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.IsMonicFaber` (`✓ std3`).

*Citation.* Erwin Miña-Díaz; Olof Rubin (2025). *Chebyshev polynomials on equipotential curves*. URL: <https://arxiv.org/abs/2505.03967v1>.

*Commentary.*

Write κ=cap(K)=1/c for the leading coefficient of ψ=φ⁻¹. A monic degree-n polynomial F is the monic Faber polynomial when F(ψ(w))−(κw)ⁿ tends to zero at infinity. Here infinity is the cobounded filter on ℂ. In the paper F_n is the polynomial part of φⁿ and F̂_n=c⁻ⁿF_n. The normalization retains the constant term as well as the leading coefficient.

**Definition 1.3 (Equality on K and on its equipotentials).**

$$claim \Leftrightarrow (\forall \psi: \mathbb{C}\to \mathbb{C}, \forall \kappa: \mathbb{R}, (0 < \kappa) \Rightarrow ((\operatorname{DifferentiableOn}\left(\mathbb{C}, \psi, \left\{w: \mathbb{C} \mid 1 < \Vert w\Vert\right\}\right)) \Rightarrow ((\operatorname{InjOn}\left(\psi, \left\{w: \mathbb{C} \mid 1 < \Vert w\Vert\right\}\right)) \Rightarrow ((\operatorname{IsCompact}\left(\operatorname{compl}\left(\operatorname{image}\left(\psi, \left\{w: \mathbb{C} \mid 1 < \Vert w\Vert\right\}\right)\right)\right)) \Rightarrow ((\exists C: \mathbb{R}, \forall w: \mathbb{C}, (2 < \Vert w\Vert) \Rightarrow (\Vert \psi\left(w\right) - (\kappa: \mathbb{C}) \cdot w\Vert \le C)) \Rightarrow (\forall n: \mathbb{N}, \forall F: \operatorname{Polynomial}\left(\mathbb{C}\right), (1 \le n) \Rightarrow ((\operatorname{IsMonicFaber}\left(\psi, \kappa, n, F\right)) \Rightarrow ((\operatorname{IsChebyshev}\left(\operatorname{compl}\left(\operatorname{image}\left(\psi, \left\{w: \mathbb{C} \mid 1 < \Vert w\Vert\right\}\right)\right), n, F\right)) \Rightarrow (\forall r: \mathbb{R}, (1 < r) \Rightarrow (\operatorname{IsChebyshev}\left(\operatorname{image}\left(\psi, \operatorname{sphere}\left(0, r\right)\right), n, F\right)))))))))))$$

*Formalization.* `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.claim` (`✓ std3`).

*Citation.* Erwin Miña-Díaz; Olof Rubin (2025). *Chebyshev polynomials on equipotential curves*. URL: <https://arxiv.org/abs/2505.03967v1>.

*Commentary.*

Section 2, Problem 2.2, states verbatim: “Suppose the compact set K is such that for some n∈ℕ, T_{n,K}=F̂_n, where F̂_n is the nth monic Faber polynomial associated to the map φ that satisfies (1.2). Is it true then that T_{n,L_r}=F̂_n for all r>1?” The unbounded component Ω of ℂ∖K has g_Ω(z,∞)=log|φ(z)|, with φ(z)=cz+c₀+c₋₁/z+… and c=cap(K)⁻¹. When Ω is simply connected, ψ=φ⁻¹ and L_r=ψ({w:|w|=r}). In the displayed statement U is {w:1<‖w‖}, K is the complement of ψ(U), and L_r is the image of the radius-r sphere. The bounded-correction hypothesis is written for ‖w‖>2; n≥1 expresses positive degree. Differentiability, injectivity, positive κ and compact complement specify the exterior-map setting.

**Theorem 1.4 (Equality need not persist).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/minadiaz-rubin-2025-chebyshev-faber-equipotential` (refuted) by `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"minadiaz-rubin-2025-chebyshev-faber-equipotential","declaration_gid":"D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Erwin Miña-Díaz; Olof Rubin (2025). *Chebyshev polynomials on equipotential curves*. URL: <https://arxiv.org/abs/2505.03967v1>.

*Commentary.*

Take ψ(w)=w+1/(4w)+(1/100)(w⁻²−w⁻⁴), κ=1, n=1 and F=X. For |u|,|v|≥1 the perturbation difference is at most (31/100)|u−v|. The power-difference bound D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le at H=1 supplies this estimate. The perturbation estimate gives injectivity on the closed exterior, an upper Lipschitz bound 131/100 and the lower bound |u−v|≤2|ψ(u)−ψ(v)|. The open mapping theorem and closedness of the closed exterior image show that K is compact and contained in the disc of radius 5/4. The boundary values ψ(±1)=±5/4 lie in K, forcing every monic linear competitor to have norm at least 5/4. Thus X is Chebyshev on K; ψ(w)−w→0 makes it the monic Faber polynomial. For r≥1 and |w|=r, the circle estimate is |ψ(w)−(1/100)(r⁻²−r⁻⁴)|≤r+1/(4r). Its proof expands the norm square on a normalized circle and bounds the cross and residual terms. At r=2, X−C(3/1600) has norm at most 17/8=3400/1600 on L₂, whereas ψ(2)=3403/1600 lies on L₂. Therefore X is not Chebyshev there. The supporting lemmas are private: perturbation_lipschitz and injective_closed supply injectivity, compact_complement supplies the compact disc containment, circle_algebra_bound and circle_bound supply the norm estimate, and chebyshev_of_disc and faber establish the initial equality. The conclusion uses one radius and does not assert a formula for the minimizer on every outer curve. Theorem 2.1's convergence as r tends to infinity is literature-attested and not formalized here; it is consistent with the centre expression tending to zero.

## References

- Truth anchor: `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.IsChebyshev`
- Truth anchor: `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.IsMonicFaber`
- Truth anchor: `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result`
- Dependency: [D5/S3/AnalyticClosure/ComplexPowerDifference](../../AnalyticClosure/ComplexPowerDifference.md)
