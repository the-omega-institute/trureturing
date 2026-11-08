# Ray distance and horizontal velocity

## Abstract

The infinitesimal Fubini-Study speed follows from the original angle distance.

The complex inner product is conjugate-linear in its first slot and linear in its second. The existing fsAngle is arccos of the norm of the complex inner product. The amplitude space is any complex inner product space; completeness and finite dimension are not required. Thus the result applies to the source's complex two-dimensional H_J once that representation has been connected.

**Definition 1.1 (Orthogonal residual of a rank-one projector).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] \forall p \in E,\; \forall z \in E,\; \operatorname{horizontal}\left(p, z\right) = z-\operatorname{apply}\left(\operatorname{rankOne}\left(\mathbb{C}, p, p\right), z\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/ProjectorRayDifferential.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This uses Mathlib's actual rankOne operator, acting as inner(p,z) times p. For unit p the residual is orthogonal to the complex line through p. The definition is not a prescribed metric.

**Theorem 1.2 (Metric speed of a differentiable unit curve).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] \forall f \in \mathbb{R}\to E,\; \forall p \in E,\; \forall v \in E,\; \Vert p\Vert = 1 \Rightarrow \left(\operatorname{apply}\left(f, 0\right) = p \Rightarrow \left(\operatorname{HasDerivAt}\left(f, v, 0\right) \Rightarrow \left(\operatorname{Eventually}\left(t\mapsto \Vert \operatorname{apply}\left(f, t\right)\Vert = 1, \operatorname{nhds}\left(0\right)\right) \Rightarrow \operatorname{Tendsto}\left(t\mapsto \frac{\operatorname{fsAngle}\left(p, \operatorname{apply}\left(f, t\right)\right)}{\lvert t\rvert}, \operatorname{puncturedNhds}\left(0\right), \operatorname{nhds}\left(\operatorname{sqrt}\left(\Vert v\Vert^{2}-\Vert \operatorname{inner}\left(\mathbb{C}, p, v\right)\Vert^{2}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ProjectorRayDifferential.fs_angle_speed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f(0) = p with norm(p) = 1, let f have real derivative v at zero, and require norm(f(t)) = 1 only in a neighbourhood of zero. Then fsAngle(p,f(t))/abs(t) tends, through nonzero real t, to sqrt(norm(v)^2 - norm(inner(p,v))^2). The curve may have arbitrary vertical phase velocity; the projection removes it. The zero horizontal-velocity case is included.

**Theorem 1.3 (The same speed from the actual projector derivative).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{C}, E\right)] \forall f \in \mathbb{R}\to E,\; \forall p \in E,\; \forall v \in E,\; \Vert p\Vert = 1 \Rightarrow \left(\operatorname{apply}\left(f, 0\right) = p \Rightarrow \left(\operatorname{HasDerivAt}\left(f, v, 0\right) \Rightarrow \left(\operatorname{Eventually}\left(t\mapsto \Vert \operatorname{apply}\left(f, t\right)\Vert = 1, \operatorname{nhds}\left(0\right)\right) \Rightarrow \operatorname{Tendsto}\left(t\mapsto \frac{\operatorname{fsAngle}\left(p, \operatorname{apply}\left(f, t\right)\right)}{\lvert t\rvert}, \operatorname{puncturedNhds}\left(0\right), \operatorname{nhds}\left(\operatorname{sqrt}\left(\operatorname{re}\left(\operatorname{trace}\left(\mathbb{C}, E, \operatorname{comp}\left(\operatorname{rankOne}\left(\mathbb{C}, p, p\right), \operatorname{comp}\left(\operatorname{deriv}\left(t\mapsto \operatorname{rankOne}\left(\mathbb{C}, \operatorname{apply}\left(f, t\right), \operatorname{apply}\left(f, t\right)\right), 0\right), \operatorname{deriv}\left(t\mapsto \operatorname{rankOne}\left(\mathbb{C}, \operatorname{apply}\left(f, t\right), \operatorname{apply}\left(f, t\right)\right), 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ProjectorRayDifferential.fs_angle_speed_projector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite complex dimension let P = rankOne(p,p), and let D be the real derivative at zero of t mapped to rankOne(f(t),f(t)), in the normed space of continuous complex-linear operators. Under the same curve hypotheses, the limit is sqrt(Re Tr(P composed with D composed with D)). The displayed formula expands these two local abbreviations. The rankOne operators are coerced to linear maps for the trace; this does not alter their action.

The derivation uses the exact identity fsAngle(p,z) = arcsin(norm(z - rankOne(p,p) z)) for unit p and z. The residual of the curve has derivative v - inner(p,v) p. Its difference quotients converge in norm. The continuous extension of arcsin(r)/r at zero has value one, which transfers this limit to the angle distance. This establishes the local distance normalization without defining the metric to equal the desired formula.

The moving-projector derivative is rankOne(p,v) + rankOne(v,p), obtained from the bounded real-bilinear rankOne map. Differentiating the local unit-norm condition gives Re inner(p,v) = 0, so D(p) is the horizontal velocity. Symmetry of D and the upstream rankOne trace formula give Tr(P D D) = norm(horizontal(p,v))^2. This identifies the diagonal real projector tensor with the speed measured by the original angle, without prescribing that speed as a definition.

The remaining OmegaQ-020 Theorem 7.3 target keeps n in the oriented unit sphere and v,w in its tangent plane. It requires the original sigma_z = -L_e R_z representation, P_n = (I + sigma_n)/2, its identification with rankOne on the original H_J, the actual derivative of P_n, and Q_n(v,w) = Tr(P_n dP_n(v) dP_n(w)) = (dot(v,w) + i dot(n,cross(v,w)))/4. Re Q must be the Fubini-Study metric with distance arccos(abs(inner(psi,phi))); Im Q must be one quarter of the oriented area. The connection uses A = i inner(psi,dpsi). For psi = (cos(theta/2), exp(i phi) sin(theta/2)), the unpaid local calculation is A = -(1-cos(theta)) dphi/2 and dA = -sin(theta) dtheta wedge dphi/2 = -2 Im Q. The global obligation retains smooth or piecewise smooth patchwise loop/surface domains, Stokes, transition winding, solid-angle ambiguity by 4 pi, and closed-loop geometric phase -Omega/2 modulo 2 pi. The local distance results alone prove none of these remaining statements. No literature originality is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ProjectorRayDifferential.fs_angle_speed`
- Truth anchor: `D5/S3/Quantum/Foundation/ProjectorRayDifferential.fs_angle_speed_projector`
- Truth anchor: `D5/S3/Quantum/Foundation/ProjectorRayDifferential.horizontal`
- Dependency: [D5/S3/QuantumBounds/FubiniStudyRecordTime](../../QuantumBounds/FubiniStudyRecordTime.md)
