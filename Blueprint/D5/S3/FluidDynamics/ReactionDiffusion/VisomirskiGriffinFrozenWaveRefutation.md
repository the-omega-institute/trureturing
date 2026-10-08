# Refutation of the Visomirski-Griffin frozen-wave conjecture

## Abstract

At the parameters a = -1/2 and D = 1/100, the alternating sine data on 50 species cannot converge to a nonhomogeneous frozen wave. The family mechanism is parity reduction to an odd Allen-Cahn profile whose energy decays when 2 n D + a is nonnegative.

**Definition 1.1 (The literal biased cycle matrix).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall j \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{biasedMatrix}\left(n, a, i, j\right) = \operatorname{ite}\left(j = \operatorname{Fin.sub}\left(i, \operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(1, 2 \cdot n\right)\right)\right), 1 + a, \operatorname{ite}\left(j = \operatorname{Fin.add}\left(i, \operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(1, 2 \cdot n\right)\right)\right), -1, 0\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.biasedMatrix` (`✓ std3`).

*Citation.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

Section 2, page 4: "If we replace each instance of +1 with 1 + a in the interaction matrix A, we obtain a biased Volterra lattice defined by the system of differential equations," and "Again, index addition and subtraction is considered modulo n." Here the cycle length is 2*n. Each row has coefficient 1+a at its predecessor, -1 at its successor, and zero elsewhere. The Fin.mk proof argument is omitted from the display; it certifies that the displayed Nat.mod value belongs to Fin (2*n). The matrix is written entrywise, as fixed in the preregistration; it is the circulant matrix with first-row entries 1 + a and −1 at the predecessor and successor positions.

**Definition 1.2 (Spatial replicator reaction).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{R},\; \forall z \in \operatorname{Fin}\left(2 \cdot n\right) \to \mathbb{R},\; \forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{reaction}\left(n, a, z, i\right) = z\left(i\right) \cdot \left(\operatorname{Matrix.mulVec}\left(\operatorname{biasedMatrix}\left(n, a\right), z\right)\left(i\right) - \operatorname{dotProduct}\left(z, \operatorname{Matrix.mulVec}\left(\operatorname{biasedMatrix}\left(n, a\right), z\right)\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.reaction` (`✓ std3`).

*Citation.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

Section 3, page 10, equation (6): u_i (e_i^T A u - u A u) + D partial_x^2 u_i. The reaction is literally formed with Matrix.mulVec and dotProduct; no simplex constraint or rewritten polynomial replaces it.

**Definition 1.3 (Alternating sine initial data).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall x \in \mathbb{R},\; \operatorname{initialData}\left(n, i, x\right) = \operatorname{ite}\left(\operatorname{Nat.mod}\left(\operatorname{val}\left(i\right), 2\right) = 0, \frac{1 + \operatorname{Real.sin}\left(x\right)}{2 \cdot (n: \mathbb{R})}, \frac{1 - \operatorname{Real.sin}\left(x\right)}{2 \cdot (n: \mathbb{R})}\right)$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.initialData` (`✓ std3`).

*Citation.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

Conjecture 2, page 19, equation (23), assigns (1+sin(x))/(2n) "if i is odd" and (1-sin(x))/(2n) "if i is even". Fin index zero is the source's species 1, so even Fin values carry the positive sine sign. Nat.mod denotes natural-number remainder, and the denominators use the real cast of n.

**Definition 1.4 (Homogeneous equilibrium).**

$$\forall n \in \mathbb{N},\; \operatorname{equilibrium}\left(n\right) = \frac{1}{2 \cdot (n: \mathbb{R})}$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.equilibrium` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

The homogeneous reference profile has the constant value 1/(2*n) for every species. This definition records only that real value.

**Definition 1.5 (Classical solution of the literal equation).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{R},\; \forall D \in \mathbb{R},\; \forall u \in \operatorname{Fin}\left(2 \cdot n\right) \to \left(\mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right)\right),\; (\operatorname{ClassicalSolution}\left(n, a, D, u\right)) \Leftrightarrow ((((((((((\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left(u\left(i\right)\right), \operatorname{Set.Ici}\left(0\right) \times \operatorname{Set.univ}\right)) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall t \in \mathbb{R},\; (0 \le t) \Rightarrow (\operatorname{Function.Periodic}\left(u\left(i\right)\left(t\right), 2 \cdot \operatorname{Real.pi}\right)))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{HasDerivAt}\left((\operatorname{fun} r: \mathbb{R} \mapsto u\left(i\right)\left(r, x\right)), \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto u\left(i\right)\left(r, x\right)), t\right), t\right)))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{HasDerivAt}\left(u\left(i\right)\left(t\right), \operatorname{deriv}\left(u\left(i\right)\left(t\right), x\right), x\right)))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{HasDerivAt}\left(\operatorname{deriv}\left(u\left(i\right)\left(t\right)\right), \operatorname{deriv}\left(\operatorname{deriv}\left(u\left(i\right)\left(t\right)\right), x\right), x\right)))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto u\left(i\right)\left(r, x\right)), t\right)))\right), \operatorname{Set.Ioi}\left(0\right) \times \operatorname{Set.univ}\right))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto \operatorname{deriv}\left(u\left(i\right)\left(t\right), x\right)))\right), \operatorname{Set.Ioi}\left(0\right) \times \operatorname{Set.univ}\right))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto \operatorname{deriv}\left(\operatorname{deriv}\left(u\left(i\right)\left(t\right)\right), x\right)))\right), \operatorname{Set.Ioi}\left(0\right) \times \operatorname{Set.univ}\right))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto u\left(i\right)\left(r, x\right)), t\right) = \operatorname{reaction}\left(n, a, (\operatorname{fun} j: \operatorname{Fin}\left(2 \cdot n\right) \mapsto u\left(j, t, x\right)), i\right) + D \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(u\left(i\right)\left(t\right)\right), x\right)))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall x \in \mathbb{R},\; u\left(i, 0, x\right) = \operatorname{initialData}\left(n, i, x\right)))$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.ClassicalSolution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

The species carrier is Fin (2*n), time and space are real, and the period is 2 Real.pi. Continuity includes time zero; the time, first space and second space derivatives exist and are jointly continuous only at positive times. The equation holds there and the alternating sine data hold at time zero. No existence or nonnegativity assumption is added.

**Definition 1.6 (Squared distance on one spatial period).**

$$\forall f \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \operatorname{distanceSq}\left(f, g\right) = \int_{-\operatorname{Real.pi}}^{\operatorname{Real.pi}} \left(f\left(x\right) - g\left(x\right)\right)^{2} dx$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.distanceSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

The squared distance is the intervalIntegral with volume from -Real.pi to Real.pi.

**Definition 1.7 (Every component approaches the homogeneous profile).**

$$\forall n \in \mathbb{N},\; \forall u \in \operatorname{Fin}\left(2 \cdot n\right) \to \left(\mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right)\right),\; (\operatorname{Homogenizes}\left(n, u\right)) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{Tendsto}\left((\operatorname{fun} t: \mathbb{R} \mapsto \operatorname{distanceSq}\left(u\left(i, t\right), \operatorname{Function.const}\left(\mathbb{R}, \operatorname{equilibrium}\left(n\right)\right)\right)), \operatorname{Filter.atTop}, \operatorname{nhds}\left(0\right)\right))$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.Homogenizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

The time limit is atTop and the target is nhds 0 for the squared distance of every species from the constant homogeneous reference profile.

**Definition 1.8 (A nonhomogeneous periodic limit).**

$$\forall n \in \mathbb{N},\; \forall u \in \operatorname{Fin}\left(2 \cdot n\right) \to \left(\mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right)\right),\; \forall v \in \operatorname{Fin}\left(2 \cdot n\right) \to \left(\mathbb{R} \to \mathbb{R}\right),\; (\operatorname{FrozenWaveLimit}\left(n, u, v\right)) \Leftrightarrow ((((\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{Continuous}\left(v\left(i\right)\right)) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{Function.Periodic}\left(v\left(i\right), 2 \cdot \operatorname{Real.pi}\right))) \land (\exists i \in \operatorname{Fin}\left(2 \cdot n\right),\; \exists x \in \mathbb{R},\; v\left(i, x\right) \ne \operatorname{equilibrium}\left(n\right))) \land (\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{Tendsto}\left((\operatorname{fun} t: \mathbb{R} \mapsto \operatorname{distanceSq}\left(u\left(i, t\right), v\left(i\right)\right)), \operatorname{Filter.atTop}, \operatorname{nhds}\left(0\right)\right)))$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.FrozenWaveLimit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

The limit has continuous 2 Real.pi-periodic components, differs from the homogeneous reference at some species and point, and is approached in squared distance by every component. The stationary equation is omitted: every stationary frozen-wave limit of the source implies this weaker predicate.

**Definition 1.9 (Conjecture 2 at the simulated parameters).**

$$(\operatorname{claim}) \Leftrightarrow (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\exists u \in \operatorname{Fin}\left(2 \cdot n\right) \to \left(\mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right)\right),\; \exists v \in \operatorname{Fin}\left(2 \cdot n\right) \to \left(\mathbb{R} \to \mathbb{R}\right),\; (\operatorname{ClassicalSolution}\left(n, -\frac{1}{2}, \frac{1}{100}, u\right)) \land (\operatorname{FrozenWaveLimit}\left(n, u, v\right))))$$

*Formalization.* `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.claim` (`✓ std3`).

*Citation.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

Conjecture 2, page 19: "Consider the one-dimensional spatial replicator, i.e., Eq. (6) with reaction term generated by a 2n-cycle with n ≥ 2. Assuming periodic boundary conditions and initial conditions of the form," followed by equation (23): u_i(x,0) = (1+sin(x))/(2n) if i is odd, and (1-sin(x))/(2n) if i is even; "the dynamics will evolve to a frozen wave stationary solution. That is, ecological niches will be maintained." The encoding fixes a = -1/2 and D = 1/100, uses index zero as species 1, and asks, for every n ≥ 2, for a classical solution and a nonhomogeneous periodic limit. It is implied by the source's frozen stationary-wave assertion at these parameters.

**Theorem 1.10 (The uniform even-cycle claim is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/visomirski-griffin-2026-frozen-wave-conjecture` (refuted) by `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"visomirski-griffin-2026-frozen-wave-conjecture","declaration_gid":"D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matthew Visomirski; Christopher Griffin (2026). *Coherent Structures and Travelling Waves in Spatial Replicators from a Biased Volterra Lattice*. DOI: [10.1016/j.chaos.2026.118260](https://doi.org/10.1016/j.chaos.2026.118260). URL: <https://arxiv.org/abs/2601.06314v1>.

*Commentary.*

At n = 25, every classical solution with the prescribed data homogenizes. Uniqueness forces shift-two invariance and the reflection exchanging the two parity classes. The parity profiles satisfy p+q=1/n and w=n*(p-q) satisfies the odd Allen-Cahn equation with mu=-a/(2*n). Its squared energy tends to zero when D ≥ mu, including the critical value n=25 at the simulated parameters. Squared-distance comparison excludes every continuous nonhomogeneous periodic limit. The result supplies no solution-existence theorem and does not decide the complementary diffusion regime, positive bias, or the per-n existential choice of parameters.

## References

- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.ClassicalSolution`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.FrozenWaveLimit`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.Homogenizes`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.biasedMatrix`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.claim`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.distanceSq`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.equilibrium`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.initialData`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.reaction`
- Truth anchor: `D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation.result`
- Dependency: [D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay](../Fourier/PeriodicAllenCahnDecay.md)
