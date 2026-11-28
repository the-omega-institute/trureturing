# Alexandrov volume and null-screen curvature

## Abstract

Null-cone rigidity and pointwise reconstruction of four-dimensional Lorentzian curvature.

In signature (−+++), the quadratic null cone determines a symmetric form up to scale. At second order in the proper time, the relative diamond volume reads the Ricci sector. The transverse trace-free tides on five distinct light rays supply the Weyl sector.

**Theorem 1.1 (Null-cone rigidity over a characteristic-zero field).**

$$((\forall k \in {K}^{4},\; ((\operatorname{q}\left(\operatorname{eta}, k\right) = 0) \implies (\operatorname{q}\left(g, k\right) = 0))) \iff \exists \omega: K, (g = \omega\,\operatorname{eta}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.conformal_metric_same_null_cone_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be any field of characteristic zero and let g be symmetric. Write eta for the diagonal matrix with entries (−1,1,1,1). The implication tests every vector k in K⁴. Write q(A,k) for kᵀAk. The six null directions with time coordinate one and a single spatial entry ±1 fix the time-space entries and all spatial diagonal entries. The three directions with time coordinate five and spatial entries three and four fix the remaining entries. Degenerate g, including the zero form, is allowed.

**Theorem 1.2 (Trace-free light-cone variation).**

$$((h = (\frac{{\operatorname{tr}}_{eta}\left(h\right)}{4}\,\operatorname{eta} + H)) \land (({\operatorname{tr}}_{eta}\left(H\right) = 0) \land ((\forall k \in {K}^{4},\; ((\operatorname{q}\left(\operatorname{eta}, k\right) = 0) \implies (\operatorname{q}\left(h, k\right) = \operatorname{q}\left(H, k\right)))) \land ((\forall k \in {K}^{4},\; ((\operatorname{q}\left(\operatorname{eta}, k\right) = 0) \implies (\operatorname{q}\left(h, k\right) = 0))) \iff (H = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.null_cone_perturbation_trace_free_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every symmetric perturbation h over the same field, let H be h minus tr_eta(h) eta/4. Then tr_eta(H) vanishes. For every eta-null k, the quadratic readings of h and H agree. All the readings vanish if and only if H is zero. The conformal line accounts for one of the ten symmetric matrix coordinates.

**Theorem 1.3 (Exact flat four-volume).**

$$(\int_{-\frac{\tau}{2}}^{\frac{\tau}{2}} \frac{4\,\pi}{3}\,{(\frac{\tau}{2} - |t|)}^{3}\,dt = \frac{\pi}{24}\,{\tau}^{4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_flat_volume` (`✓ std3`). ∎

*Citation.* G. W. Gibbons and S. N. Solodukhin (2007). *The Geometry of Small Causal Diamonds*. DOI: [10.1016/j.physletb.2007.03.068](https://doi.org/10.1016/j.physletb.2007.03.068). URL: <https://arxiv.org/abs/hep-th/0703098>.

*Commentary.*

For real proper time tau at least zero, put r(t) = tau/2 − |t|. The cross section at time t has Euclidean three-ball volume 4 pi r(t)³/3. Splitting the interval at zero gives two equal integrals.

**Theorem 1.4 (Time and per-coordinate spatial moments).**

$$((\int_{-\frac{\tau}{2}}^{\frac{\tau}{2}} {t}^{2}\,\frac{4\,\pi}{3}\,{(\frac{\tau}{2} - |t|)}^{3}\,dt = \frac{{\tau}^{2}}{60}\,\frac{\pi}{24}\,{\tau}^{4}) \land (\int_{-\frac{\tau}{2}}^{\frac{\tau}{2}} \frac{4\,\pi}{15}\,{(\frac{\tau}{2} - |t|)}^{5}\,dt = \frac{{\tau}^{2}}{30}\,\frac{\pi}{24}\,{\tau}^{4}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_quadratic_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real proper time tau at least zero, reflection eliminates mixed moments. Each spatial coordinate has the same second moment in the three-ball. Integrating the angular mean of x_i² gives 4 pi r(t)⁵/15. The time and per-coordinate spatial moments are respectively tau²/60 and tau²/30 times the flat four-volume.

**Theorem 1.5 (The quadratic density on the fixed domain).**

$$(-\frac{1}{6}\,({A}_{00}\,{M}_{t} + (({A}_{11} + {A}_{22}) + {A}_{33})\,{M}_{x}) = \frac{\pi}{24}\,{\tau}^{4}\,{\tau}^{2}\,(-\frac{{A}_{00}}{120} - \frac{{\operatorname{tr}}_{eta}\left(A\right)}{180}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_bulk_ricci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real matrix A and real tau at least zero, let M_t be the time moment and M_x the per-coordinate spatial moment given by the preceding integrals. The bulk density contribution uses A_00 M_t plus (A_11 + A_22 + A_33) M_x, all multiplied by −1/6.

**Theorem 1.6 (The radial displacement in midpoint normal coordinates).**

$$(\operatorname{HasDerivAtZero}\left(({(r + \varepsilon\,v)}^{2}\,(1 - \varepsilon\,\frac{{\tau}^{2}\,E}{12}) - {r}^{2}), 0\right) \iff (v = \frac{{\tau}^{2}\,E\,r}{24}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_boundary_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take real tau, r, E and v with r positive. In the truncated null equation, E is the curvature reading on the spatial direction and the time leg. The trial displacement is epsilon times v. The equation has zero first-order residual exactly at the displayed radial velocity.

**Theorem 1.7 (First variation of the moving boundary).**

$$\operatorname{HasDerivAtZero}\left(\int_{-\frac{\tau}{2}}^{\frac{\tau}{2}} \sum_{i} \frac{4\,\pi}{9}\,{(\frac{\tau}{2} - |t|)\,(1 + \varepsilon\,\frac{{\tau}^{2}\,{E}_{i}}{24})}^{3}\,dt, \frac{\frac{\pi}{24}\,{\tau}^{4}\,{\tau}^{2}\,\sum_{i} {E}_{i}}{24}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_boundary_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real tau at least zero, let E be the three diagonal spatial sectional readings. The angular mean of n_i n_j is delta_ij/3, so the three axis values give the angular mean at degree two. The volume derivative at epsilon zero uses the cubic radial variation and the flat volume.

**Theorem 1.8 (The bulk and boundary coefficient).**

$$\operatorname{HasDerivAtZero}\left(\operatorname{truncatedRNCVolume}\left(R, \tau\right), \frac{\pi}{24}\,{\tau}^{4}\,{\tau}^{2}\,D\left(R, {e}_{0}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_rnc_volume_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an algebraic curvature tensor R and real tau at least zero, take E_i = R_0i0i in the moving boundary model, and A = Ric(R) in the fixed-domain density. Add the moving-boundary volume to epsilon times the bulk contribution. At epsilon zero its derivative is the flat volume times tau² times D(R,e_0). Here D is the signed relative volume correction and e_0 = (1,0,0,0). This model retains the quadratic normal-coordinate density and first-order radial displacement. The spatial moments and spherical means supply the cross-section reductions for these interval integrals. The smooth spacetime interpretation uses the small-diamond expansion and its remainder estimates.

**Definition 1.9 (Directional coefficient).**

$$(D\left(R, u\right) = (\frac{\operatorname{Ric}\left(R, u, u\right)}{30} + \frac{\operatorname{Scal}\left(R\right)\,\operatorname{minkowski}\left(u, u\right)}{180}))$$

*Formalization.* `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrovO2Deficit` (`✓ std3`).

*Citation.* G. W. Gibbons and S. N. Solodukhin (2007). *The Geometry of Small Causal Diamonds*. DOI: [10.1016/j.physletb.2007.03.068](https://doi.org/10.1016/j.physletb.2007.03.068). URL: <https://arxiv.org/abs/hep-th/0703098>.

*Commentary.*

Define D on algebraic curvature and all real directions. For unit timelike u the coefficient multiplies squared proper time in the relative volume change. Scalar curvature uses the Minkowski trace of Ricci curvature.

**Theorem 1.10 (Every Weyl tensor has zero volume coefficient).**

$$(D\left(W, u\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_o2_weyl_blind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every W in the algebraic Weyl space and every real direction u, the Ricci contraction and its trace vanish.

**Theorem 1.11 (Unit timelike readings separate the Ricci sector).**

$$((\forall u \in {\mathbb{R}}^{4},\; ((\operatorname{minkowski}\left(u, u\right) = -1) \implies (D\left(R, u\right) = 0))) \iff ((\operatorname{ricciPart}\left(R\right) = 0) \land (\operatorname{scalarPart}\left(R\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_o2_reconstructs_ricci_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every algebraic curvature tensor R, vanishing in all unit timelike directions is equivalent to the simultaneous vanishing of trace-free Ricci and scalar curvature. The proof tests the rest direction, six axial boosts and three directions with two nonzero spatial entries. These evaluations recover the quadratic form Ric(R) + Scal(R) eta/6. Its trace recovers Scal(R).

**Theorem 1.12 (Joint reconstruction of all twenty components).**

$$(((\forall u \in {\mathbb{R}}^{4},\; ((\operatorname{minkowski}\left(u, u\right) = -1) \implies (D\left(R, u\right) = 0))) \land (\forall i \in \operatorname{Fin}\left(5\right),\; (\operatorname{complexTide}\left(R, \operatorname{r}\left(i\right)\right) = 0))) \iff (R = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.complete_curvature_reconstruction_volume_and_five_rays` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every algebraic curvature tensor R and every family r of five distinct future null rays, the joint kernel is zero. Volume detects the Ricci sector. Equal Ricci shifts on the two screen diagonal entries cancel in the complex tide. Quartic interpolation on the five rays detects the remaining Weyl component. For at most four rays, the Weyl quartic vanishing construction gives a nonzero curvature with zero tide at every sampled ray and zero volume reading in every direction. The observations are specified pointwise on the tangent space. Applying the result to a discrete causal order requires a separate rule for obtaining the tidal observations from its comparisons.

**Theorem 1.13 (A polarized Ricci-flat wave).**

$$((W \neq 0) \land ((\forall u \in {\mathbb{R}}^{4},\; (D\left(W, u\right) = 0)) \land (\operatorname{complexTide}\left(W, \operatorname{some}\left(1\right)\right) \neq 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.volume_blind_nonzero_weyl_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Weyl tensor W has electric block diag(1,−1,0) and magnetic entries M_01 = M_10 = 1, with all other magnetic entries zero. Its volume coefficient vanishes in every real direction and its complex screen tide at the finite ray with coordinate one is nonzero.

**Theorem 1.14 (Scalar curvature invisible to every screen).**

$$(({R}_{s} \neq 0) \land ((\operatorname{weylPart}\left({R}_{s}\right) = 0) \land ((\forall r \in \operatorname{FutureNullRay},\; (\operatorname{complexTide}\left({R}_{s}, r\right) = 0)) \land (D\left({R}_{s}, {e}_{0}\right) = -\frac{1}{72}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.screen_blind_nonzero_ricci_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor R_s has scalar curvature one and zero Weyl and trace-free Ricci parts. It is nonzero, has zero complex tide on every future null ray, and has a signed volume coefficient −1/72 in the rest direction.

**Theorem 1.15 (Independent prescription of volume and tides).**

$$\exists R, ((\operatorname{ricciPart}\left(R\right) = 0) \land ((D\left(R, {e}_{0}\right) = v) \land (\forall i \in \operatorname{Fin}\left(5\right),\; (\operatorname{complexTide}\left(R, \operatorname{r}\left(i\right)\right) = T\left(i\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.rest_volume_and_five_tides_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every family r of five distinct future null rays, every real v and every function T from Fin 5 to the complex numbers, there is an algebraic curvature tensor with zero trace-free Ricci part, rest-frame volume coefficient v, and complex tides T. Interpolate the five values in the Weyl sector and scale the scalar tensor by −72v to set the volume value.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrovO2Deficit`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_boundary_radius`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_boundary_volume`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_bulk_ricci`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_flat_volume`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_quadratic_moments`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_diamond_rnc_volume_coefficient`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_o2_reconstructs_ricci_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.alexandrov_o2_weyl_blind`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.complete_curvature_reconstruction_volume_and_five_rays`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.conformal_metric_same_null_cone_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.null_cone_perturbation_trace_free_split`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.rest_volume_and_five_tides_surjective`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.screen_blind_nonzero_ricci_witness`
- Truth anchor: `D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D.volume_blind_nonzero_weyl_witness`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
