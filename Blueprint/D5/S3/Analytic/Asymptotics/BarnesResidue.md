# A Barnes contour shift

## Abstract

A single-pole contour shift has the dy normalization 2*pi.

**Theorem 1.1 (The single-pole shift).**

$$\forall phi \in Complex \to Complex,\; \forall c1 \in Real,\; \forall c2 \in Real,\; \forall p \in Complex,\; \left(c1 < re\left(p\right) \land \left(re\left(p\right) < c2 \land \left(DifferentiableOn\left(Complex, phi, preimage\left(re, Icc\left(c1, c2\right)\right)\right) \land \left(Integrable\left((y:Real \mapsto (s:Complex \mapsto \frac{phi\left(s\right)}{(s-p)})\left((c1+(y*\operatorname{ComplexI}))\right))\right) \land \left(Integrable\left((y:Real \mapsto (s:Complex \mapsto \frac{phi\left(s\right)}{(s-p)})\left((c2+(y*\operatorname{ComplexI}))\right))\right) \land \left(Tendsto\left((T:Real \mapsto intervalIntegral\left((x:Real \mapsto (s:Complex \mapsto \frac{phi\left(s\right)}{(s-p)})\left((x+(T*\operatorname{ComplexI}))\right)), c1, c2\right)), atTop, nhds\left(0\right)\right) \land Tendsto\left((T:Real \mapsto intervalIntegral\left((x:Real \mapsto (s:Complex \mapsto \frac{phi\left(s\right)}{(s-p)})\left((x+(T*\operatorname{ComplexI}))\right)), c1, c2\right)), atBot, nhds\left(0\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow (integral\left((y:Real \mapsto (s:Complex \mapsto \frac{phi\left(s\right)}{(s-p)})\left((c2+(y*\operatorname{ComplexI}))\right))\right)-integral\left((y:Real \mapsto (s:Complex \mapsto \frac{phi\left(s\right)}{(s-p)})\left((c1+(y*\operatorname{ComplexI}))\right))\right)) = ((2*\pi )*phi\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/BarnesResidue.barnesRes_vertical_shift` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

The rectangle argument subtracts the removable divided difference of phi at p. The remaining reciprocal kernel has the arctangent/logarithm primitive. Horizontal terms vanish, and the two vertical reciprocal limits give exactly 2*pi times phi(p), with integration in dy.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/BarnesResidue.barnesRes_vertical_shift`
