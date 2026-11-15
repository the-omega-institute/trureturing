# Sharp conditioned rank-one optimization

## Abstract

Clipped weights attain the sharp condition-constrained complex essential-sup bound for positive rank-one evolutions.

Let mu be an arbitrary nonzero finite measure on a measurable space X. The real function h is essentially bounded and strictly positive almost everywhere. Write H=lpNorm(h,infinity,mu)>0 and Q=integral(h squared)>0. Atomic measures are included. All operator inputs are complex; no spatial attainment of H or positive essential floor of h is assumed. The rank-one map is P f=h integral(h f)/Q, and T_a=a I+(1-a)P for 0<=a<=1. This is a variational synthesis from essential-sup bounds and Bochner integral comparison. External novelty and current openness of this formula are unverified.

**Definition 1.1 (Every equivalent positive weight).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall g: (X)\to \mathbb{R}, (\operatorname{Weight}\left(mu, g\right)) \Leftrightarrow ((\operatorname{MemLp}\left(g, \infty, mu\right)) \land ((\operatorname{MemLp}\left((x: X)\mapsto \operatorname{inv}\left(\operatorname{apply}\left(g, x\right)\right), \infty, mu\right)) \land (\operatorname{AE}\left(mu, (x: X)\mapsto 0 < \operatorname{apply}\left(g, x\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.Weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Weight consists of essential boundedness of g and 1/g and strict positivity almost everywhere. MemLp includes AE strong measurability; all measurable weights are included.

**Definition 1.2 (The multiplication condition number).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall g: (X)\to \mathbb{R}, \operatorname{condition}\left(mu, g\right) = \operatorname{lpNorm}\left(g, \infty, mu\right) \cdot \operatorname{lpNorm}\left((x: X)\mapsto \operatorname{inv}\left(\operatorname{apply}\left(g, x\right)\right), \infty, mu\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.condition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is invariant under positive scalar rescaling.

**Definition 1.3 (Complex rank-one evolution).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall a: \mathbb{R}, \forall f: (X)\to \mathbb{C}, \forall x: X, \operatorname{apply}\left(\operatorname{evolve}\left(mu, h, a, f\right), x\right) = \operatorname{ofReal}\left(a\right) \cdot \operatorname{apply}\left(f, x\right) + \left(1 - \operatorname{ofReal}\left(a\right)\right) \cdot \operatorname{divide}\left(\operatorname{ofReal}\left(\operatorname{apply}\left(h, x\right)\right) \cdot \operatorname{integral}\left((y: X)\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(h, y\right)\right) \cdot \operatorname{apply}\left(f, y\right), mu\right), \operatorname{ofReal}\left(\operatorname{integral}\left((x: X)\mapsto \operatorname{apply}\left(h, x\right)^{2}, mu\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.evolve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evolve(mu,h,a,f) uses the actual complex integral and its real squared normalization Q. The theorem proves Q positive before dividing.

**Definition 1.4 (All inputs and an attaining witness).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall a: \mathbb{R}, \forall g: (X)\to \mathbb{R}, \forall C: \mathbb{R}, (\operatorname{Sharp}\left(mu, h, a, g, C\right)) \Leftrightarrow ((0 \le C) \land ((\forall f: (X)\to \mathbb{C}, ((\operatorname{MemLp}\left(f, \infty, mu\right)) \land (\operatorname{MemLp}\left(f, 2, mu\right))) \Rightarrow (\operatorname{eLpNorm}\left((x: X)\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(g, x\right)\right) \cdot \operatorname{apply}\left(\operatorname{evolve}\left(mu, h, a, f\right), x\right), \infty, mu\right) \le \operatorname{ofReal}\left(C\right) \cdot \operatorname{eLpNorm}\left((x: X)\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(g, x\right)\right) \cdot \operatorname{apply}\left(f, x\right), \infty, mu\right))) \land (\exists f: (X)\to \mathbb{C}, ((\operatorname{MemLp}\left(f, \infty, mu\right)) \land (\operatorname{MemLp}\left(f, 2, mu\right))) \land ((\operatorname{eLpNorm}\left((x: X)\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(g, x\right)\right) \cdot \operatorname{apply}\left(f, x\right), \infty, mu\right) = 1) \land (\operatorname{eLpNorm}\left((x: X)\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(g, x\right)\right) \cdot \operatorname{apply}\left(\operatorname{evolve}\left(mu, h, a, f\right), x\right), \infty, mu\right) = \operatorname{ofReal}\left(C\right))))))$$

*Formalization.* `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.Sharp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sharp uses genuine eLpNorm inequalities for every bounded complex L2 input and an actual attaining input of weighted norm one. It is not defined by the scalar formula.

**Definition 1.5 (The clipped feasible weight).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall H: \mathbb{R}, \forall kappa: \mathbb{R}, \forall x: X, \operatorname{apply}\left(\operatorname{clipped}\left(h, H, kappa\right), x\right) = \operatorname{inv}\left(\operatorname{max}\left(1, \operatorname{divide}\left(kappa \cdot \operatorname{apply}\left(h, x\right), H\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.clipped` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the theorem parameters 1/kappa<=g star<=1 and 1<=1/g star<=kappa almost everywhere. Its condition number can be strictly below kappa, for example for constant h.

**Definition 1.6 (The explicit optimum value).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall a: \mathbb{R}, \forall kappa: \mathbb{R}, \operatorname{optimum}\left(mu, h, a, kappa\right) = 1 + \operatorname{divide}\left(1 - a, \operatorname{integral}\left((x: X)\mapsto \operatorname{apply}\left(h, x\right)^{2}, mu\right)\right) \cdot \operatorname{integral}\left((x: X)\mapsto \operatorname{apply}\left(h, x\right) \cdot \operatorname{max}\left(\operatorname{divide}\left(\operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right) - \operatorname{apply}\left(h, x\right), 0\right), mu\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.optimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q is the integral of h squared and H is the actual lpNorm of h at infinity. The deficit is the integral of h times max(H/kappa-h,0).

**Theorem 1.7 (The all-weight essential envelope).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall g: (X)\to \mathbb{R}, \forall kappa: \mathbb{R}, (((\operatorname{NeZero}\left(mu\right)) \land (\operatorname{MemLp}\left(h, \infty, mu\right))) \land ((\operatorname{Weight}\left(mu, g\right)) \land ((1 \le kappa) \land (\operatorname{condition}\left(mu, g\right) \le kappa)))) \Rightarrow (\operatorname{AE}\left(mu, (x: X)\mapsto \operatorname{max}\left(\operatorname{apply}\left(h, x\right), \operatorname{divide}\left(\operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right)\right) \le \operatorname{divide}\left(\operatorname{lpNorm}\left((x: X)\mapsto \operatorname{apply}\left(g, x\right) \cdot \operatorname{apply}\left(h, x\right), \infty, mu\right), \operatorname{apply}\left(g, x\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing G=norm infinity g, B=norm infinity 1/g and c=norm infinity gh, H<=Bc, gh<=c and g<=G with GB<=kappa force c/g>=max(h,H/kappa). No point attaining H is assumed.

**Theorem 1.8 (The genuine fixed-weight sharp norm).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall g: (X)\to \mathbb{R}, \forall a: \mathbb{R}, (((\operatorname{IsFiniteMeasure}\left(mu\right)) \land ((\operatorname{NeZero}\left(mu\right)) \land ((\operatorname{MemLp}\left(h, \infty, mu\right)) \land (\operatorname{AE}\left(mu, (x: X)\mapsto 0 < \operatorname{apply}\left(h, x\right)\right))))) \land ((\operatorname{Weight}\left(mu, g\right)) \land ((0 \le a) \land (a \le 1)))) \Rightarrow (\operatorname{Sharp}\left(mu, h, a, g, a + \operatorname{divide}\left(\left(1 - a\right) \cdot \operatorname{lpNorm}\left((x: X)\mapsto \operatorname{apply}\left(g, x\right) \cdot \operatorname{apply}\left(h, x\right), \infty, mu\right) \cdot \operatorname{integral}\left((x: X)\mapsto \operatorname{divide}\left(\operatorname{apply}\left(h, x\right), \operatorname{apply}\left(g, x\right)\right), mu\right), \operatorname{integral}\left((x: X)\mapsto \operatorname{apply}\left(h, x\right)^{2}, mu\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.fixed_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex integral modulus bound proves the estimate for every input. The actual input f=1/g belongs to L2 and L infinity, has weighted norm one, and attains a+(1-a)c integral(h/g)/Q. An affine essential-sup identity supplies equality.

**Theorem 1.9 (Sharp minimum, excess and all minimizers).**

$$\forall X: \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(X\right)]\forall mu: \operatorname{Measure}\left(X\right), \forall h: (X)\to \mathbb{R}, \forall kappa: \mathbb{R}, \forall a: \mathbb{R}, (((\operatorname{IsFiniteMeasure}\left(mu\right)) \land ((\operatorname{NeZero}\left(mu\right)) \land ((\operatorname{MemLp}\left(h, \infty, mu\right)) \land (\operatorname{AE}\left(mu, (x: X)\mapsto 0 < \operatorname{apply}\left(h, x\right)\right))))) \land ((1 \le kappa) \land ((0 \le a) \land (a \le 1)))) \Rightarrow ((\operatorname{Weight}\left(mu, \operatorname{clipped}\left(h, \operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right)\right)) \land ((\operatorname{condition}\left(mu, \operatorname{clipped}\left(h, \operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right)\right) \le kappa) \land ((\operatorname{Sharp}\left(mu, h, a, \operatorname{clipped}\left(h, \operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right), \operatorname{optimum}\left(mu, h, a, kappa\right)\right)) \land (\forall g: (X)\to \mathbb{R}, ((\operatorname{Weight}\left(mu, g\right)) \land (\operatorname{condition}\left(mu, g\right) \le kappa)) \Rightarrow (\exists C: \mathbb{R}, (\operatorname{Sharp}\left(mu, h, a, g, C\right)) \land ((\operatorname{optimum}\left(mu, h, a, kappa\right) \le C) \land ((C - \operatorname{optimum}\left(mu, h, a, kappa\right) = \operatorname{divide}\left(1 - a, \operatorname{integral}\left((x: X)\mapsto \operatorname{apply}\left(h, x\right)^{2}, mu\right)\right) \cdot \operatorname{integral}\left((x: X)\mapsto \operatorname{apply}\left(h, x\right) \cdot \operatorname{abs}\left(\operatorname{divide}\left(\operatorname{lpNorm}\left((x: X)\mapsto \operatorname{apply}\left(g, x\right) \cdot \operatorname{apply}\left(h, x\right), \infty, mu\right), \operatorname{apply}\left(g, x\right)\right) - \operatorname{max}\left(\operatorname{apply}\left(h, x\right), \operatorname{divide}\left(\operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right)\right)\right), mu\right)) \land (((a < 1) \Rightarrow ((C = \operatorname{optimum}\left(mu, h, a, kappa\right)) \Leftrightarrow (\exists s: \mathbb{R}, (0 < s) \land (\operatorname{AE}\left(mu, (x: X)\mapsto \operatorname{apply}\left(g, x\right) = s \cdot \operatorname{apply}\left(\operatorname{clipped}\left(h, \operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right), x\right)\right))))) \land (((a = 1) \Rightarrow (C = 1)) \land ((a < 1) \Rightarrow ((\operatorname{optimum}\left(mu, h, a, kappa\right) = 1) \Leftrightarrow (\operatorname{AE}\left(mu, (x: X)\mapsto \operatorname{divide}\left(\operatorname{lpNorm}\left(h, \infty, mu\right), kappa\right) \le \operatorname{apply}\left(h, x\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.conditioned_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same clipped weight attains the minimum for every a. The excess is exactly (1-a)/Q times the integral of h times absolute(c/g-max(h,H/kappa)). Integral-zero rigidity makes all minimizers for a<1 positive scalar multiples of the clipped weight modulo AE equality. For a<1 the minimum equals one exactly when h>=H/kappa almost everywhere. At a=1 every admissible weight has sharp constant one. This weighted L1 identity gives no L infinity stability estimate. The actual interval semigroup consumes the theorem in its owner. A distinct finite atomic check on a two-point space with counting measure uses a=0, h=(1/4,1), kappa=2 and projection optimum 18/17.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.Sharp`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.Weight`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.clipped`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.condition`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.conditioned_optimum`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.envelope`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.evolve`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.fixed_weight`
- Truth anchor: `D5/S3/Quantum/Semigroups/ConditionedRankOneNorm.optimum`
