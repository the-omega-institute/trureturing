# Null-cone closure and horizon focusing

## Abstract

Flat-chart horizon thermodynamics and optical focusing in four dimensions.

**Theorem 1.1 (Null-cone rigidity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall S \in \operatorname{Mat}_{4\times4}\left(K\right),\; ((S)^{T} = S \implies ((\forall k \in K^{4},\; (\sum_{a} (\operatorname{eta}\left(a, a\right) \cdot (k\left(a\right) \cdot k\left(a\right))) = 0 \implies \sum_{a} \sum_{b} (k\left(a\right) \cdot (S\left(a, b\right) \cdot k\left(b\right))) = 0)) \iff (\exists c \in K,\; S = (c \cdot \operatorname{eta}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.symmetric_null_vanishing_iff_smul_eta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the metric η = diag(−1,1,1,1). The two null rays in each time–space plane give equal spatial diagonal entries and eliminate each time–space entry. For each spatial pair, a null vector with time component 5 and spatial components 3 and 4 then eliminates the mixed spatial entry. The argument works over every field of characteristic zero.

**Theorem 1.2 (One integration constant).**

$$\forall U \in \operatorname{Set}\left(\mathbb{R}^{4}\right),\; \forall R \in (\mathbb{R}^{4} \to \operatorname{Mat}_{4\times4}\left(\mathbb{R}\right)),\; \forall T \in (\mathbb{R}^{4} \to \operatorname{Mat}_{4\times4}\left(\mathbb{R}\right)),\; \forall c \in \mathbb{R},\; \forall E \in (\mathbb{R}^{4} \to \operatorname{Mat}_{4\times4}\left(\mathbb{R}\right)),\; \forall p \in (\mathbb{R}^{4} \to \mathbb{R}),\; (((\forall y \in \mathbb{R}^{4},\; (E\left(y\right) = (R\left(y\right) - (\frac{\operatorname{MinkowskiTrace}\left(R\left(y\right)\right)}{2} \cdot \operatorname{eta})) \land p\left(y\right) = (R\left(y\right) - (c \cdot T\left(y\right)))\left(0, 0\right))) \land (\operatorname{Open}\left(U\right) \land \operatorname{Preconnected}\left(U\right) \land (\forall x \in \mathbb{R}^{4},\; ((x \in U) \implies (\operatorname{DifferentiableEntriesAt}\left(R, x\right) \land \operatorname{DifferentiableEntriesAt}\left(T, x\right) \land (R\left(x\right))^{T} = R\left(x\right) \land (T\left(x\right))^{T} = T\left(x\right) \land (\forall k \in \mathbb{R}^{4},\; (\operatorname{eta}\left(k, k\right) = 0 \implies (((k)^{T} \cdot (R\left(x\right) - (c \cdot T\left(x\right)))) \cdot k) = 0)) \land (\forall b \in \operatorname{Fin}\left(4\right),\; (\operatorname{div}\left(E, x, b\right) = 0 \land \operatorname{div}\left(T, x, b\right) = 0))))))) \implies ((\forall x \in \mathbb{R}^{4},\; ((x \in U) \implies \operatorname{HasFDerivAt}\left(y \mapsto (p\left(y\right) + \frac{\operatorname{MinkowskiTrace}\left(R\left(y\right)\right)}{2}), 0, x\right))) \land (\exists l \in \mathbb{R},\; \forall x \in \mathbb{R}^{4},\; ((x \in U) \implies (E\left(x\right) + (l \cdot \operatorname{eta})) = (c \cdot T\left(x\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.jacobson_bianchi_einstein_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the preconnected open domain U, the coupling is c and the matrix fields R and T are symmetric. Their entries are differentiable at each point. Write E = R − trη(R)η/2 and p = (R − cT)₀₀. Null-cone rigidity applied to the symmetric residual gives cT − R = pη on U. The contracted derivative div uses Σₐ ηₐₐ ∂ₐ in the first slot of each matrix field. The Bianchi and conservation equations force each coordinate derivative of p + trη(R)/2 to vanish. That scalar is locally constant and hence constant on U. This is the flat-chart form of the algebraic closure in Jacobson's Thermodynamics of Spacetime (1995), culminating in his Eq. (6).

**Theorem 1.3 (Vacuum cosmological-constant indeterminacy).**

$$\forall c \in \mathbb{R},\; \forall l \in \mathbb{R},\; \forall m \in \mathbb{R},\; \forall R \in (\mathbb{R} \to (\mathbb{R}^{4} \to \operatorname{Mat}_{4\times4}\left(\mathbb{R}\right))),\; \forall T \in (\mathbb{R}^{4} \to \operatorname{Mat}_{4\times4}\left(\mathbb{R}\right)),\; \forall E \in (\mathbb{R} \to (\mathbb{R}^{4} \to \operatorname{Mat}_{4\times4}\left(\mathbb{R}\right))),\; (((l \neq m) \land ((\forall x \in \mathbb{R}^{4},\; T\left(x\right) = 0) \land (\forall p \in \mathbb{R},\; \forall x \in \mathbb{R}^{4},\; (R\left(p, x\right) = (p \cdot \operatorname{eta}) \land E\left(p, x\right) = (R\left(p, x\right) - (\frac{\operatorname{MinkowskiTrace}\left(R\left(p, x\right)\right)}{2} \cdot \operatorname{eta})))))) \implies ((\forall p \in \mathbb{R},\; \forall x \in \mathbb{R}^{4},\; ((\forall k \in \mathbb{R}^{4},\; (\operatorname{eta}\left(k, k\right) = 0 \implies (((k)^{T} \cdot (R\left(p, x\right) - (c \cdot T\left(x\right)))) \cdot k) = 0)) \land (\forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{div}\left(E\left(p\right), x, b\right) = 0) \land (E\left(p, x\right) + (p \cdot \operatorname{eta})) = 0)) \land (\forall x \in \mathbb{R}^{4},\; \forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{div}\left(T, x, b\right) = 0) \land (R\left(l\right) \neq R\left(m\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.cosmological_constant_indeterminacy_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the constant Ricci field R(λ) = λη, the trace is 4λ. With T = 0 the null contractions and both divergences vanish everywhere and E + λη = 0. The 00 entry distinguishes R(λ) from R(μ) for distinct constants.

**Theorem 1.4 (Expansion and shear focusing).**

$$\forall f \in (\mathbb{R} \to \mathbb{R}),\; \forall s \in (\mathbb{R} \to \mathbb{C}),\; \forall p \in (\mathbb{R} \to \mathbb{R}),\; \forall t \in \mathbb{R},\; ((\operatorname{HasDerivAt}\left(f, ((- \frac{(f\left(t\right))^{2}}{2} - (\Vert s\left(t\right) \Vert)^{2}) - p\left(t\right)), t\right) \land (0 \le p\left(t\right))) \implies ((f'\left(t\right) \le - \frac{(f\left(t\right))^{2}}{2}) \land (- \frac{(f\left(t\right))^{2}}{2} \le 0) \land ((s\left(t\right) \neq 0) \implies (f'\left(t\right) < - \frac{(f\left(t\right))^{2}}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.raychaudhuri_monotonic_focusing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At time t, p is the null Ricci flux and s is the complex shear. The squared shear norm and the nonnegative Ricci flux both reduce the derivative of the expansion f.

**Theorem 1.5 (Finite affine ceiling).**

$$\forall f \in (\mathbb{R} \to \mathbb{R}),\; \forall L \in \mathbb{R},\; (((0 \le L) \land (f\left(0\right) < 0) \land \operatorname{ContinuousOn}\left(f, [0, L]\right) \land \operatorname{DifferentiableOn}\left(f, (0, L)\right) \land (\forall t \in \mathbb{R},\; ((t \in (0, L)) \implies (f'\left(t\right) \le - \frac{(f\left(t\right))^{2}}{2})))) \implies ((\forall t \in \mathbb{R},\; ((t \in [0, L]) \implies ((f\left(t\right) < 0) \land (\frac{t}{2} \le (\frac{1}{f\left(t\right)} - \frac{1}{f\left(0\right)})) \land (f\left(t\right) \le \frac{f\left(0\right)}{(1 + (\frac{f\left(0\right)}{2} \cdot t))})))) \land (L < \frac{- 2}{f\left(0\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.hawking_penrose_caustic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity up to both endpoints and the interior differential inequality make the initially negative expansion f nonincreasing. Its reciprocal minus t/2 is nondecreasing. The reciprocal stays strictly negative for a finite expansion, which gives a strict endpoint bound. The denominator in the pointwise comparison is positive throughout the interval.

**Theorem 1.6 (Sharpness of the ceiling).**

$$\forall T \in \mathbb{R},\; ((0 < T) \implies (\forall f \in (\mathbb{R} \to \mathbb{R}),\; ((\forall t \in \mathbb{R},\; ((t < T) \implies f\left(t\right) = \frac{- 2}{(T - t)})) \implies ((f\left(0\right) < 0) \land T = \frac{- 2}{f\left(0\right)} \land (\forall t \in \mathbb{R},\; ((t < T) \implies (\operatorname{HasDerivAt}\left(f, - \frac{(f\left(t\right))^{2}}{2}, t\right) \land (\frac{1}{f\left(t\right)} - \frac{1}{f\left(0\right)}) = \frac{t}{2})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.hawking_penrose_caustic_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive pole position T, the function f(t) = −2/(T − t) solves the equality throughout t < T and attains the reciprocal comparison with equality. Its restriction gives a finite solution on every [0,L] with 0 < L < T.

**Theorem 1.7 (Stationary optical rigidity).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall f \in (\mathbb{R} \to \mathbb{R}),\; \forall s \in (\mathbb{R} \to \mathbb{C}),\; \forall p \in (\mathbb{R} \to \mathbb{R}),\; \forall w \in (\mathbb{R} \to \mathbb{C}),\; ((\forall t \in \mathbb{R},\; ((t \in (a, b)) \implies (\operatorname{HasDerivAt}\left(f, ((- \frac{(f\left(t\right))^{2}}{2} - (\Vert s\left(t\right) \Vert)^{2}) - p\left(t\right)), t\right) \land \operatorname{HasDerivAt}\left(s, (- (\operatorname{ofReal}\left(f\left(t\right)\right) \cdot s\left(t\right)) - w\left(t\right)), t\right) \land (0 \le p\left(t\right)) \land f\left(t\right) = 0))) \implies (\forall t \in \mathbb{R},\; ((t \in (a, b)) \implies (p\left(t\right) = 0 \land s\left(t\right) = 0 \land w\left(t\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.stationary_horizon_shear_weyl_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The expansion f vanishes on an open interval, so its derivative there vanishes. Nonzero shear would give a strictly negative expansion derivative. With shear zero, Raychaudhuri gives zero Ricci flux p. The Sachs equation then forces the Weyl tidal component w driving that shear to vanish on the same interval.

**Theorem 1.8 (Stationary QFC and QNEC).**

$$\forall G \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall f \in (\mathbb{R} \to \mathbb{R}),\; \forall s \in (\mathbb{R} \to \mathbb{C}),\; \forall p \in (\mathbb{R} \to \mathbb{R}),\; \forall A \in (\mathbb{R} \to \mathbb{R}),\; \forall S \in (\mathbb{R} \to \mathbb{R}),\; \forall H \in (\mathbb{R} \to \mathbb{R}),\; \forall h \in \mathbb{R},\; (((0 < G) \land (0 < A\left(t\right)) \land (\exists r \in \mathbb{R},\; ((0 < r) \land (\forall u \in \mathbb{R},\; ((\Vert (u - t) \Vert < r) \implies \operatorname{HasDerivAt}\left(A, (f\left(u\right) \cdot A\left(u\right)), u\right))))) \land (\exists r \in \mathbb{R},\; ((0 < r) \land (\forall u \in \mathbb{R},\; ((\Vert (u - t) \Vert < r) \implies \operatorname{HasDerivAt}\left(S, H\left(u\right), u\right))))) \land \operatorname{HasDerivAt}\left(H, h, t\right) \land \operatorname{HasDerivAt}\left(f, ((- \frac{(f\left(t\right))^{2}}{2} - (\Vert s\left(t\right) \Vert)^{2}) - p\left(t\right)), t\right) \land f\left(t\right) = 0 \land s\left(t\right) = 0) \implies ((\exists r \in \mathbb{R},\; ((0 < r) \land (\forall u \in \mathbb{R},\; ((\Vert (u - t) \Vert < r) \implies \operatorname{HasDerivAt}\left((u \mapsto (\frac{A\left(u\right)}{(4 \cdot G)} + S\left(u\right))), (u \mapsto (\frac{(f\left(u\right) \cdot A\left(u\right))}{(4 \cdot G)} + H\left(u\right)))\left(u\right), u\right))))) \land \operatorname{HasDerivAt}\left((u \mapsto (\frac{(f\left(u\right) \cdot A\left(u\right))}{(4 \cdot G)} + H\left(u\right))), (- (\frac{A\left(t\right)}{(4 \cdot G)} \cdot p\left(t\right)) + h), t\right) \land (((- (\frac{A\left(t\right)}{(4 \cdot G)} \cdot p\left(t\right)) + h) \le 0) \iff ((\frac{(4 \cdot G)}{A\left(t\right)} \cdot h) \le p\left(t\right))) \land (\forall x \in \mathbb{R},\; (p\left(t\right) = (((8 \cdot \operatorname{pi}) \cdot G) \cdot x) \implies (((- (\frac{A\left(t\right)}{(4 \cdot G)} \cdot p\left(t\right)) + h) \le 0) \iff (\frac{h}{((2 \cdot \operatorname{pi}) \cdot A\left(t\right))} \le x))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.qfc_iff_qnec_at_stationary_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one affine generator, take area A, expansion f, shear s, flux p, and outside entropy S. The first derivative of A is fA near the evaluation parameter t. At zero expansion and shear the second derivative of the area is −A(t)p(t). With A(t)>0 and G>0, the sign of the second generalized entropy variation gives the single-generator stationary bound. The normalized quantum expansion has the same derivative sign at this point since A′(t)=0. The Ricci flux is 8πG times the null stress. This is the stationary diagonal relation considered by Bousso et al. in Quantum Focusing (2016), §5.2.

**Theorem 1.9 (Area assigned to basis pinching).**

$$\forall N \in \operatorname{Type},\; [\operatorname{Fintype}\left(N\right)] [\operatorname{DecidableEq}\left(N\right)] \forall G \in \mathbb{R},\; \forall q \in \operatorname{DensityState}\left(N\right),\; ((0 < G) \implies (((4 \cdot G) \cdot (\operatorname{S}\left(\operatorname{P}\left(q\right)\right) - \operatorname{S}\left(q\right))) = ((4 \cdot G) \cdot \operatorname{D}\left(q, \operatorname{P}\left(q\right)\right)) \land (0 \le ((4 \cdot G) \cdot (\operatorname{S}\left(\operatorname{P}\left(q\right)\right) - \operatorname{S}\left(q\right)))) \land (\forall i \in N,\; \forall j \in N,\; (((i \neq j) \land (\operatorname{matrix}\left(q\right)\left(i, j\right) \neq 0)) \implies (0 < ((4 \cdot G) \cdot (\operatorname{S}\left(\operatorname{P}\left(q\right)\right) - \operatorname{S}\left(q\right)))))) \land (((4 \cdot G) \cdot (\operatorname{S}\left(\operatorname{P}\left(q\right)\right) - \operatorname{S}\left(q\right))) = 0 \iff \operatorname{matrix}\left(\operatorname{P}\left(q\right)\right) = \operatorname{matrix}\left(q\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.clausius_area_monotonicity_from_record_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite density state ρ let P(ρ) be its diagonal pinching and let A and B be their matrices before and after pinching. Assign the area change ΔA = 4G(S(P(ρ)) − S(ρ)). The entropy identity gives relative entropy D(ρ∥P(ρ)). Positivity of A implies that a zero diagonal entry forces the whole corresponding column to vanish. Therefore the kernel of B is contained in the kernel of A. The spectral-ceiling Klein inequality bounds D from below by a positive multiple of the squared Hilbert–Schmidt distance. The area change vanishes exactly when pinching fixes the matrix, and is positive for any deleted nonzero off-diagonal entry.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.clausius_area_monotonicity_from_record_pinching`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.cosmological_constant_indeterminacy_counterexample`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.hawking_penrose_caustic_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.hawking_penrose_caustic_sharpness`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.jacobson_bianchi_einstein_equation`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.qfc_iff_qnec_at_stationary_horizon`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.raychaudhuri_monotonic_focusing`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.stationary_horizon_shear_weyl_rigidity`
- Truth anchor: `D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D.symmetric_null_vanishing_iff_smul_eta`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
- Dependency: [D5/S3/Quantum/Divergence/SpectralCeilingRelativeEntropy](../../Quantum/Divergence/SpectralCeilingRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
