# Actual endpoint samples and a uniform error bound

## Abstract

Finite mesh approximation of the Robin mass

Write M(A,B) for the weighted negative mass of the tail of the actual Chebyshev kernel (ψ(t)−t)/t². The mesh x is strictly increasing on the natural indices from 0 through N.

**Definition 1.1 (Weighted chord mass).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{C}\left(a, b\right) = \int_{a}^{b} \operatorname{w}\left(t\right) \cdot \operatorname{max}\left(\operatorname{H}\left(a, b, t\right), 0\right) dt$$

*Formalization.* `D5/S3/Weil/Mertens/RobinFiniteMesh.chordMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For u(t)=t log(t), write Q(a,b,t)=(u(t)−u(a))/(u(b)−u(a)) and H(a,b,t)=(1−Q(a,b,t))R(a)+Q(a,b,t)R(b). The weight is w(t)=(log(t)/(1+log(t)))/(t sqrt(t)). On the meshes below, each signed ramp sample has the finite Mangoldt formula of RobinWeightedRamp.ramp_eq_sum with a cutoff at least the floor of its endpoint.

**Theorem 1.2 (Endpoint error bound).**

$$\forall A \in \mathbb{R},\; \forall B \in \mathbb{R},\; \forall h \in \mathbb{R},\; \forall N \in \mathbb{N},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \operatorname{exp}\left(1\right) \le A \Rightarrow \left(B \le 2 \cdot A \Rightarrow \left(\operatorname{x}\left(0\right) = A \Rightarrow \left(\operatorname{x}\left(N\right) = B \Rightarrow \left(\left(\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; i \le N \Rightarrow \left(j \le N \Rightarrow \left(i < j \Rightarrow \operatorname{x}\left(i\right) < \operatorname{x}\left(j\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; i < N \Rightarrow \operatorname{x}\left(i + 1\right) - \operatorname{x}\left(i\right) \le h\right) \Rightarrow \left|\operatorname{M}\left(A, B\right) - (\sum_{0 \le i \land i < N} \operatorname{C}\left(\operatorname{x}\left(i\right), \operatorname{x}\left(i + 1\right)\right))\right| \le \frac{3 \cdot h^{2}}{4 \cdot A^{2} \cdot \operatorname{sqrt}\left(A\right)} \cdot (\operatorname{psi}\left(B\right) - \operatorname{psi}\left(A\right) + B - A)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinFiniteMesh.abs_mass_sub_mesh_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On each cell [a,b], monotonicity of ψ puts ψ(t)−t between ψ(a)−b and ψ(b)−a. Sum the centered chord estimates with a common mesh coefficient. Adjacent interval integrals recover M(A,B), and the widths sum to ψ(B)−ψ(A)+B−A.

**Theorem 1.3 (Uniform error at the three-quarter-power mesh scale).**

$$\forall A \in \mathbb{R},\; \forall B \in \mathbb{R},\; \forall h \in \mathbb{R},\; \forall eta \in \mathbb{R},\; \forall N \in \mathbb{N},\; \forall x \in \mathbb{N} \to \mathbb{R},\; \operatorname{exp}\left(1\right) \le A \Rightarrow \left(B \le 2 \cdot A \Rightarrow \left(\operatorname{x}\left(0\right) = A \Rightarrow \left(\operatorname{x}\left(N\right) = B \Rightarrow \left(\left(\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; i \le N \Rightarrow \left(j \le N \Rightarrow \left(i < j \Rightarrow \operatorname{x}\left(i\right) < \operatorname{x}\left(j\right)\right)\right)\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; i < N \Rightarrow \operatorname{x}\left(i + 1\right) - \operatorname{x}\left(i\right) \le h\right) \Rightarrow \left(h \le eta \cdot A^{\frac{3}{4}} \Rightarrow \left|\operatorname{M}\left(A, B\right) - (\sum_{0 \le i \land i < N} \operatorname{C}\left(\operatorname{x}\left(i\right), \operatorname{x}\left(i + 1\right)\right))\right| \le 9 \cdot eta^{2}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/RobinFiniteMesh.abs_mass_sub_mesh_le_nine_mul_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unconditional Chebyshev bound ψ(B)≤(11/2)B makes the endpoint budget at most 12A. Squaring the step scale cancels A sqrt(A) in the common coefficient. For the empty mesh, both masses vanish.

## References

- Truth anchor: `D5/S3/Weil/Mertens/RobinFiniteMesh.abs_mass_sub_mesh_le`
- Truth anchor: `D5/S3/Weil/Mertens/RobinFiniteMesh.abs_mass_sub_mesh_le_nine_mul_sq`
- Truth anchor: `D5/S3/Weil/Mertens/RobinFiniteMesh.chordMass`
- Dependency: [D5/S3/Weil/Mertens/RobinCenteredChord](RobinCenteredChord.md)
