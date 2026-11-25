# Antipodal certificate for two cosine constraints

## Abstract

The attained minimum sampled cosine gives an exact root of the finite dual certificate.

**Definition 1.1 (Angular spacing).**

$$\forall q \in Nat,\; \operatorname{h}\left(q\right) = \frac{2 \cdot \pi}{q}$$

*Formalization.* `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.mesh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive modulus q, the mesh is the angular difference between adjacent residues.

**Definition 1.2 (Centered cosine sample).**

$$\forall q \in Nat,\; \forall i \in \operatorname{ZMod}\left(q\right),\; \operatorname{c}\left(i\right) = \operatorname{cos}\left(\operatorname{CenteredAngle}\left(i\right)\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered angle uses the integer representative in the half-open centered interval.

**Theorem 1.3 (The two roots and the energy identity).**

$$\operatorname{c}\left(\operatorname{HalfFloor}\left(q\right)\right) = C \land \left(\left(\forall i \in \operatorname{ZMod}\left(q\right),\; C \le \operatorname{c}\left(i\right) \land \left(\operatorname{p}\left(i\right) = \frac{H \cdot \left(\operatorname{c}\left(i\right) - C\right) \cdot \left(\operatorname{c}\left(i\right) - rho\right)}{Z} \land \left(0 < \operatorname{PositivePart}\left(\operatorname{p}\left(i\right)\right) \Leftrightarrow \left(C < \operatorname{c}\left(i\right) \land rho < \operatorname{c}\left(i\right)\right)\right)\right)\right) \land \left(\forall v \in \operatorname{Feasible}\left(q, a\right),\; \operatorname{E}\left(v\right) = \operatorname{B}\left(a\right) + \operatorname{R}\left(v\right) + 2 \cdot \operatorname{J}\left(v\right) + \frac{2 \cdot beta}{Z} \cdot \left(\operatorname{M}\left(1, v\right) - a\right) + \frac{H}{Z} \cdot \left(\operatorname{M}\left(2, v\right) - a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.antipodal_dual_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q, let h=2π/q, d=(q mod 2)/2 and C=−cos(dh). The centered representative floor(q/2) attains C. Every centered representative has absolute value at most floor(q/2), so the cosine is at least C.

For H,Z>0 and C<1, set β=(t−H(1−C²))/(1−C), ρ=−C−β/H and p(i)=(t−H(1−c(i)²)−β(1−c(i)))/Z. Write p₊ for the positive part. The factorization holds even when the two roots coincide. A sample at C has p₊=0.

The energy identity applies to every feasible v at threshold a. B is the dual bound 2(t−(H/2+β)(1−a))/Z−Σ p₊², R is Σ(v−p₊)², and J is Σv(p₊−p). The two moment slacks are M₁(v)−a and M₂(v)−a. The identity gives E(v)≥B when β≥0.

**Definition 1.4 (Mass transfer).**

$$\forall q \in Nat,\; \forall w \in \operatorname{Weights}\left(q\right),\; \forall delta \in Real,\; \forall mu \in Real,\; \forall s \in Real,\; \forall i \in \operatorname{ZMod}\left(q\right),\; \operatorname{Adjusted}\left(w, delta, mu, s, i\right) = \operatorname{w}\left(i\right) - \left(delta + mu\right) \cdot \operatorname{Indicator}\left(0, i\right) + s \cdot \operatorname{Indicator}\left(1, i\right) + s \cdot \operatorname{Indicator}\left(-1, i\right) + mu \cdot \operatorname{Indicator}\left(\operatorname{HalfFloor}\left(q\right), i\right)$$

*Formalization.* `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.adjusted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The indicator at each listed residue acts on the corresponding scalar increment. The closest antipodal residue chosen here has centered representative floor(q/2) for q>0.

**Theorem 1.5 (Exact matching of the two deficits).**

$$\operatorname{Feasible}\left(q, 1 - A, \operatorname{Adjusted}\left(w, delta, mu, \frac{delta}{2}\right)\right) \land \left(\operatorname{M}\left(1, \operatorname{Adjusted}\left(w, delta, mu, \frac{delta}{2}\right)\right) = 1 - A \land \operatorname{M}\left(2, \operatorname{Adjusted}\left(w, delta, mu, \frac{delta}{2}\right)\right) = 1 - A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.adjusted_matches_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q≥4 and let w be nonnegative with mass one. Define Dᵣ=1−Mᵣ(w), F=1−cos(h), G=1−cos(2h), U=1−C and V=2(1−C²). For target deficit A, take δ=(A−D₂−V(A−D₁)/U)/(G−VF/U) and μ=(A−D₁−Fδ)/U. Both denominators are positive for q≥4.

Assume w(0)−δ−μ≥0, w(1)+δ/2≥0, w(−1)+δ/2≥0 and μ≥0. The transfer gives a feasible v at threshold 1−A, with equality in both moments. The moment increments in deficit coordinates are Fδ+Uμ and Gδ+Vμ. Both equations follow by substitution, and the four increments sum to zero.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.adjusted`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.adjusted_matches_moments`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.antipodal_dual_certificate`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.mesh`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicParityCorrection.sample`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison](CyclicToLatticeComparison.md)
