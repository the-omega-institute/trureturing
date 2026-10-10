# Decay of odd periodic Allen-Cahn profiles

## Abstract

Odd real classical profiles on the circle satisfy the Allen-Cahn energy identity and converge in squared L2 energy to zero when diffusion dominates nonnegative linear growth, including equality of the two rates.

**Definition 1.1 (Scalar regularity).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; (\operatorname{ScalarRegular}\left(w\right)) \Leftrightarrow ((((((((\operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left(w\right), \operatorname{Set.Ici}\left(0\right) \times \operatorname{Set.univ}\right)) \land (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow (\operatorname{Function.Periodic}\left(w\left(t\right), 2 \cdot \operatorname{Real.pi}\right)))) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{HasDerivAt}\left((\operatorname{fun} r: \mathbb{R} \mapsto w\left(r, x\right)), \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto w\left(r, x\right)), t\right), t\right)))) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{HasDerivAt}\left(w\left(t\right), \operatorname{deriv}\left(w\left(t\right), x\right), x\right)))) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{HasDerivAt}\left(\operatorname{deriv}\left(w\left(t\right)\right), \operatorname{deriv}\left(\operatorname{deriv}\left(w\left(t\right)\right), x\right), x\right)))) \land (\operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto w\left(r, x\right)), t\right)))\right), \operatorname{Set.Ioi}\left(0\right) \times \operatorname{Set.univ}\right))) \land (\operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto \operatorname{deriv}\left(w\left(t\right), x\right)))\right), \operatorname{Set.Ioi}\left(0\right) \times \operatorname{Set.univ}\right))) \land (\operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto \operatorname{deriv}\left(\operatorname{deriv}\left(w\left(t\right)\right), x\right)))\right), \operatorname{Set.Ioi}\left(0\right) \times \operatorname{Set.univ}\right)))$$

*Formalization.* `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.ScalarRegular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile is continuous for nonnegative time, periodic with period 2 Real.pi, and has time, first space and second space derivatives for positive time. All three derivative functions are jointly continuous there. The record imposes no equation or initial data.

**Definition 1.2 (Squared energy on one period).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall t \in \mathbb{R},\; \operatorname{energy}\left(w, t\right) = \int_{-\operatorname{Real.pi}}^{\operatorname{Real.pi}} w\left(t, x\right)^{2} dx$$

*Formalization.* `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is volume and the integral is the oriented intervalIntegral from -Real.pi to Real.pi.

**Lemma 1.3 (Continuity of a time slice).**

$$\forall F \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall s \in \operatorname{Set}\left(\mathbb{R}\right),\; \forall r \in \operatorname{Set}\left(\mathbb{R}\right),\; \forall t \in \mathbb{R},\; ((\operatorname{ContinuousOn}\left(\operatorname{Function.uncurry}\left(F\right), s \times r\right)) \land (t \in s)) \Rightarrow (\operatorname{ContinuousOn}\left(F\left(t\right), r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.slice_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity on a product restricts to a continuous spatial slice at any time belonging to the time set.

**Lemma 1.4 (Zero initial energy stays zero).**

$$\forall Y \in \mathbb{R} \to \mathbb{R},\; \forall Z \in \mathbb{R} \to \mathbb{R},\; \forall T \in \mathbb{R},\; \forall K \in \mathbb{R},\; (((((\operatorname{ContinuousOn}\left(Y, \operatorname{Set.Icc}\left(0, T\right)\right)) \land (\forall t \in \mathbb{R},\; (t \in \operatorname{Set.Ioo}\left(0, T\right)) \Rightarrow (\operatorname{HasDerivAt}\left(Y, Z\left(t\right), t\right)))) \land (\forall t \in \mathbb{R},\; (t \in \operatorname{Set.Ioo}\left(0, T\right)) \Rightarrow (Z\left(t\right) \le K \cdot Y\left(t\right)))) \land (Y\left(0\right) = 0)) \land (\forall t \in \mathbb{R},\; (t \in \operatorname{Set.Icc}\left(0, T\right)) \Rightarrow (0 \le Y\left(t\right)))) \Rightarrow (\forall t \in \mathbb{R},\; (t \in \operatorname{Set.Icc}\left(0, T\right)) \Rightarrow (Y\left(t\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy_zero_of_gronwall` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity at the endpoints and the differential inequality on the open time interval suffice. No derivative at time zero is required.

**Lemma 1.5 (Continuous spatial slices).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall t \in \mathbb{R},\; ((\operatorname{ScalarRegular}\left(w\right)) \land (0 \le t)) \Rightarrow (\operatorname{Continuous}\left(w\left(t\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.slice_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative time slice of a scalar regular profile is continuous on the whole real line.

**Lemma 1.6 (Energy is continuous in time).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; (\operatorname{ScalarRegular}\left(w\right)) \Rightarrow (\operatorname{ContinuousOn}\left(\operatorname{energy}\left(w\right), \operatorname{Set.Ici}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Joint continuity on nonnegative time and compactness of a spatial period give continuity of the energy including at time zero.

**Lemma 1.7 (Nonnegative squared energy).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall t \in \mathbb{R},\; 0 \le \operatorname{energy}\left(w, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The increasing interval endpoints make the integral of a square nonnegative, without any regularity assumption on the profile.

**Lemma 1.8 (Diffusion and forcing energy identity).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall t \in \mathbb{R},\; \forall D \in \mathbb{R},\; \forall Q \in \mathbb{R} \to \mathbb{R},\; ((((\operatorname{ScalarRegular}\left(w\right)) \land (0 < t)) \land (\operatorname{Continuous}\left(Q\right))) \land (\forall x \in \mathbb{R},\; \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto w\left(r, x\right)), t\right) = D \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(w\left(t\right)\right), x\right) + Q\left(x\right))) \Rightarrow (\operatorname{HasDerivAt}\left(\operatorname{energy}\left(w\right), 2 \cdot \int_{-\operatorname{Real.pi}}^{\operatorname{Real.pi}} w\left(t, x\right) \cdot Q\left(x\right) dx - 2 \cdot D \cdot \int_{-\operatorname{Real.pi}}^{\operatorname{Real.pi}} \operatorname{deriv}\left(w\left(t\right), x\right)^{2} dx, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.pde_energy_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a continuous forcing term at a fixed positive time, periodic integration by parts gives the derivative-square contribution -2*D times its integral; this contribution is nonpositive when D is nonnegative.

**Theorem 1.9 (Odd Allen-Cahn evolution decays).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall D \in \mathbb{R},\; \forall mu \in \mathbb{R},\; ((((((\operatorname{ScalarRegular}\left(w\right)) \land (0 < D)) \land (0 \le mu)) \land (mu \le D)) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto w\left(r, x\right)), t\right) = D \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(w\left(t\right)\right), x\right) + mu \cdot \left(w\left(t, x\right) - w\left(t, x\right)^{3}\right)))) \land (\forall t \in \mathbb{R},\; (0 < t) \Rightarrow (\forall x \in \mathbb{R},\; w\left(t, -x\right) = -w\left(t, x\right)))) \Rightarrow (\operatorname{Tendsto}\left(\operatorname{energy}\left(w\right), \operatorname{Filter.atTop}, \operatorname{nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.odd_allen_cahn_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd profile has zero spatial mean. Parseval and the derivative formula for Fourier coefficients give the first-eigenvalue inequality. The energy identity then yields exponential decay for mu < D and a quadratic differential inequality with reciprocal decay for mu = D > 0. The conclusion is a limit for every scalar regular solution satisfying the displayed hypotheses; existence is not asserted.

**Lemma 1.10 (Regularity under subtraction).**

$$\forall f \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall g \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; ((\operatorname{ScalarRegular}\left(f\right)) \land (\operatorname{ScalarRegular}\left(g\right))) \Rightarrow (\operatorname{ScalarRegular}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto f\left(t, x\right) - g\left(t, x\right)))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting two scalar regular profiles preserves their regularity and period.

**Lemma 1.11 (Regularity under reflection).**

$$\forall w \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; (\operatorname{ScalarRegular}\left(w\right)) \Rightarrow (\operatorname{ScalarRegular}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto w\left(t, -x\right)))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.reflect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Spatial reflection changes the sign of the first derivative and preserves the second derivative.

**Lemma 1.12 (Regularity under affine combinations).**

$$\forall f \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall g \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; ((\operatorname{ScalarRegular}\left(f\right)) \land (\operatorname{ScalarRegular}\left(g\right))) \Rightarrow (\operatorname{ScalarRegular}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto a \cdot f\left(t, x\right) + b \cdot g\left(t, x\right) + c))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constant affine combinations preserve scalar regularity.

**Lemma 1.13 (Time and second space derivatives of affine combinations).**

$$\forall f \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall g \in \mathbb{R} \to \left(\mathbb{R} \to \mathbb{R}\right),\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall x \in \mathbb{R},\; (((\operatorname{ScalarRegular}\left(f\right)) \land (\operatorname{ScalarRegular}\left(g\right))) \land (0 < t)) \Rightarrow ((\operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto (\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto a \cdot f\left(t, x\right) + b \cdot g\left(t, x\right) + c))\left(r, x\right)), t\right) = a \cdot \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto f\left(r, x\right)), t\right) + b \cdot \operatorname{deriv}\left((\operatorname{fun} r: \mathbb{R} \mapsto g\left(r, x\right)), t\right)) \land (\operatorname{deriv}\left(\operatorname{deriv}\left((\operatorname{fun} t: \mathbb{R} \mapsto (\operatorname{fun} x: \mathbb{R} \mapsto a \cdot f\left(t, x\right) + b \cdot g\left(t, x\right) + c))\left(t\right)\right), x\right) = a \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(f\left(t\right)\right), x\right) + b \cdot \operatorname{deriv}\left(\operatorname{deriv}\left(g\left(t\right)\right), x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.affine_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant term has zero derivatives and the two other terms differentiate linearly.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.ScalarRegular`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.affine`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.affine_derivatives`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy_continuous`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy_nonnegative`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.energy_zero_of_gronwall`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.odd_allen_cahn_decay`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.pde_energy_deriv`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.reflect`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.slice_continuous`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.slice_continuousOn`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay.sub`
