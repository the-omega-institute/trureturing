# Angular certificates for the two-mode Wu cubic deficit

## Abstract

Matched and refined angular bounds for the physical ordinary-trace cubic deficit.

For the equal-cap, exponent-three specialization of Wu v1, Remark 3.15, equation (3.54), use the signed CAR jumps E₀₁−E₂₃ and E₀₂+E₁₃, r = exp(β/3), and an embedded spectrum (m,n,q,1) with 0 ≤ m ≤ n ≤ q ≤ 1. The unitary U supplies an arbitrary complex orthonormal frame in occupation order. Let a = 2t₀, b = 2t₃, S = a+b and F = a−b, where tᵢ is the odd occupation of the i-th frame line. Let v be the absolute charge of the lower pair, u its odd offset, and w = 1−v. The Lean even offset is −u. Write D₀₂ for the symmetric crossing between the two extreme lines.

**Theorem 1.1 (Product bound for the extreme crossing).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.long_crossing_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.long_crossing_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The two extreme lines satisfy F²/4 ≤ S D₀₂. The complex determinant estimate uses P = √((1−t₀)t₃) and Q = √(t₀(1−t₃)) with D₀₂ ≥ (P−Q)², (P+Q)² ≤ 2(t₀+t₃), and P²−Q² = t₃−t₀.

**Theorem 1.2 (Angular long-crossing weight).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.long_crossing_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.long_crossing_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Define f(S) = max(1,1/S) for S ≠ 0 and f(0) = 0. The estimate D₀₂ ≥ f(S)F²/4 follows from the product bound and (P+Q)² ≤ 1. It is equation (1) of the lower Gibbs complement proof, with the zero-tilt case included. In particular no division by S is needed in the product form.

Use nonnegative diagonal cut weights Aᵢ and bias weights Bᵢ, two adjacent coefficients Z₀ = Z₀₁ and Z₂ = Z₁₂, and long coefficient Zlong = Z₀₂. The retained cost includes the diagonal cuts, signed upper-projection charges, adjacent crossings and Zlong D₀₂. Its occupation reference is 2∑ Aᵢ−∑ Bᵢ+Z₀+Z₂. Put L₀ = B₁/2−A₁, κ = Zlong/4, Pᵢ = (Aᵢ+Zᵢ−L₀)/2 and Gᵢ = Bᵢ/2−2Pᵢ for i = 0,2. Write C = P₀a²+P₂b²+G₀a+G₂b for the matched singleton correction.

**Theorem 1.3 (Matched angular estimate for the cuts).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.matched_cut_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.matched_cut_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

If 0 ≤ L₀ ≤ min(Z₀,Z₂) and Zlong ≥ 0, the same absolute adjacent weight L₀ is used on both sides. The middle quadratic coefficient is then A₁+L₀ = B₁/2. The w terms reduce to B₁w²/2 and the u terms to (3A₁+L₀)u²+L₀Fu. Completing the u square gives the retained cost lower bound occupation cost + C + (κ f(S)−L₀/4)F².

**Theorem 1.4 (Common endpoint charge).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_charge_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_charge_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let L be a nonnegative common adjacent weight, ℓ = L−L₀ and H = A₁+L with A₁ ≥ 0. If HS/2 ≤ ℓ ≤ min(B₀,B₂), then μ = ℓ−HS/2 lies in [0,min(B₀,B₂)]. The same multiplier can therefore be used in both singleton charge inequalities of the physical frame.

**Theorem 1.5 (Refined angular estimate for the cuts).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_cut_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_cut_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Take L = min(Z₀,Z₂), under the matched mixture conditions, nonnegative Aᵢ, B₁ and Zlong, and the common charge admissibility condition. After the common charge is inserted the w terms are Hw²−HS w and the linear singleton terms gain HS²/2. The change of singleton weights contributes −ℓ(S²+F²)/4 after the linear cancellation. Completing the w square leaves (H−ℓ)S²/4 = B₁S²/8. Completing the u square loses L²F²/[4(3A₁+L)]. The retained cost is at least occupation cost + C + B₁S²/8 + (κ f(S)−ℓ/4−L²/[4(3A₁+L)])F². The middle-square loss is zero when L = 0.

**Theorem 1.6 (Ordinary-trace operator identity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.normalized_deficit_eq_ordinary_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.normalized_deficit_eq_ordinary_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Relabel the unitary U by the two-mode occupation pairs to obtain V, and set M = V diag(m,n,q,1) V* and X = G(r)⁻¹ M G(r)⁻¹ using the operator bridge Gibbs factor G. For r ≥ 1 the normalized spectral source deficit δ is exactly (9/8) Re tr(M² G(r) generator(r,X) G(r)) − α(r) (Re tr(M³(log(M³)−log D(r))) − Re tr(M³) log(Re tr(M³))). The logarithms are the spectral functional calculus and tr is ordinary trace. The identity identifies the left-hand deficit of the angular estimates with the source energy minus entropy in the cubic specialization of Wu v1 (3.54).

**Theorem 1.7 (Exact signed spectral cut expansion).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.normalized_deficit_eq_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.normalized_deficit_eq_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For r ≥ 1 and nonnegative levels the physical deficit equals the thermal and entropy center plus the retained cost and the three directed corrections. The diagonal coefficients are cutEnergy and cutBias, the adjacent coefficients are lowerCoeff and upperCoeff, and the long coefficient is longCoeff with the extra middle gap q−n. The directed terms are proportional to w₂₀+w₃₀, w₃₀+w₃₁ and w₃₀, where wᵢⱼ is the sum of squared jump amplitudes from column j to i. For ordered levels these corrections are nonnegative.

**Theorem 1.8 (Occupation deficit identity).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.occupation_deficit_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.occupation_deficit_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At U = 1 the directed corrections and the long crossing vanish, and the physical deficit of the same spectrum equals δocc, the thermal and entropy center plus the occupation cut cost. This reference retains the same spectrum and the same ordinary-trace normalization.

**Theorem 1.9 (Matched inequality for the physical deficit).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.matched_deficit_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.matched_deficit_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For r ≥ 1, ordered nonnegative levels bounded by one, and 0 ≤ L₀ ≤ min(Z₀,Z₂) for the physical cut coefficients, δ ≥ δocc + C + (κ f(S)−L₀/4)F². This is equation (2) of the lower Gibbs complement proof. The exact signed cut identity permits dropping the nonnegative directed terms.

**Theorem 1.10 (Refined inequality and the common tilt gain).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_deficit_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_deficit_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

With the same physical cut coefficients and the further condition HS/2 ≤ ℓ ≤ min(B₀,B₂), equation (3) is δ ≥ δocc + C + B₁S²/8 + (κ f(S)−ℓ/4−L²/[4(3A₁+L)])F². The extra B₁S²/8 belongs to the actual deficit from the ordinary-trace operator identity. In the closed lower Gibbs region proof (research source wu-cubic-lower-gibbs-complement/proof.txt, equations (2)–(3)), the range is 26/25 ≤ r ≤ 7/5 with m ≤ r⁻². Near g = (r⁻²,r⁻¹,r⁻¹,1), let d = maxᵢ |xᵢ−gᵢ|. For 0 < d ≤ 1/256 and 1049/1000 ≤ r ≤ 7/5, the proof uses (2) for S ≥ dK and (3) for S ≤ dK. It checks P₀,P₂ > 0 and κ ≥ L₀/4, chooses K from G₀/d, G₂/d and the Pᵢ, and verifies HdK/2 ≤ ℓ ≤ min(B₀,B₂) on the small-tilt branch. The extra gain changes the coefficient of S² in the small-tilt quadratic to (P₀+P₂+B₁/2)/4. This is the quadratic used by the lower Gibbs proof before its Gibbs-relative minimization and exact interval replay. The Lean theorem supplies the physical frame inequality conditional on those coefficient and charge comparisons. The full temperature and spectral cover is established in the cited research proof by separate exact replays.

**Theorem 1.11 (Repeated middle level).**

Lean statement: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.repeated_middle_angular_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.repeated_middle_angular_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

When q = n and 0 ≤ m ≤ n ≤ 1, A₁, B₁, Z₀, Z₂, L₀, L and μ vanish. Both mixture and charge conditions hold in every complex frame for r ≥ 1. The refined gain and mixture losses vanish, leaving δ ≥ δocc + singletonCorrection(U,A,B,0,0,0) + κ f(S)F². The nonzero end gaps can still contribute through the long crossing, so this reduction includes the zero middle gap without division by that gap.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.long_crossing_ge`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.long_crossing_mul`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.matched_cut_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.matched_deficit_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.normalized_deficit_eq_cuts`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.normalized_deficit_eq_ordinary_trace`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.occupation_deficit_eq`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_charge_admissible`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_cut_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.refined_deficit_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.repeated_middle_angular_bound`
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicCoupledCuts](WuCubicCoupledCuts.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicOperatorBridge](WuCubicOperatorBridge.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing](WuCubicSharpLongCrossing.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuCubicSignedTransfer](WuCubicSignedTransfer.md)
