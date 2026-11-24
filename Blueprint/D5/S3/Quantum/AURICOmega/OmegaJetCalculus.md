# Rational jet calculus and formal differential equations

## Abstract

Second-order jets in Chapter 32, section 32.7.3.1, the secant identity in section 32.7.5.3, and formal rational series in section 32.8.4.4.

**Theorem 1.1 (The jet increment cubes to zero).**

$$\operatorname{Equivalent}\left(eta^{3}, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.var_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variable is the second-order jet with coefficients (0, 1, 0). Multiplication retains degrees zero, one and two.

**Theorem 1.2 (Inversion of a second-order jet).**

$$\forall a \in Jet2,\; \left(\operatorname{Unit}\left(\operatorname{coeff}\left(a, 0\right)\right) \land \left(\operatorname{Finite}\left(\operatorname{coeff}\left(a, 1\right)\right) \land \operatorname{Finite}\left(\operatorname{coeff}\left(a, 2\right)\right)\right)\right) \Rightarrow \operatorname{Equivalent}\left(a \cdot \operatorname{inv}\left(a\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.mul_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An invertible constant coefficient is a finite nonzero fraction. The inverse of a normalized jet 1 + u has coefficients obtained from 1 - u + u squared because u cubed vanishes.

**Theorem 1.3 (First and second chain rules at zero shift).**

$$\forall g \in Jet2, f \in Jet2,\; \left(\operatorname{Finite}\left(\operatorname{coeff}\left(g, 1\right)\right) \land \left(\operatorname{Finite}\left(\operatorname{coeff}\left(g, 2\right)\right) \land \left(\operatorname{Finite}\left(f\right) \land \operatorname{Equivalent}\left(\operatorname{coeff}\left(f, 0\right), 0\right)\right)\right)\right) \Rightarrow \left(\operatorname{Equivalent}\left(\operatorname{first}\left(\operatorname{compose}\left(g, f\right)\right), \operatorname{first}\left(g\right) \cdot \operatorname{first}\left(f\right)\right) \land \operatorname{Equivalent}\left(\operatorname{second}\left(\operatorname{compose}\left(g, f\right)\right), \operatorname{second}\left(g\right) \cdot \operatorname{first}\left(f\right)^{2} + \operatorname{first}\left(g\right) \cdot \operatorname{second}\left(f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.chain_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer jet is evaluated in the inner jet, whose constant coefficient is zero. The second derivative is twice the quadratic coefficient.

**Theorem 1.4 (The exact fidelity jet).**

$$\forall x \in IntRatio,\; \operatorname{Equivalent}\left(\operatorname{kappaJetAt}\left(x\right), (\operatorname{kappa}\left(x\right), \frac{-2 \cdot x}{\left(1 + x^{2}\right)^{2}}, \frac{3 \cdot x^{2} - 1}{\left(1 + x^{2}\right)^{3}})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.kappa_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inverting the jet of 1 + (x + eta) squared gives the three coefficients for kappa, where kappa(x) is the reciprocal of 1 + x squared.

**Theorem 1.5 (The fidelity jet at one).**

$$\operatorname{Equivalent}\left(\operatorname{kappaJetAt}\left(1\right), (\frac{1}{2}, -\frac{1}{2}, \frac{1}{4})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.kappa_jet_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient triple at one gives the value, the linear coefficient and the quadratic coefficient in that order.

**Theorem 1.6 (The exact secant discrepancy).**

$$\forall x \in IntRatio, h \in IntRatio,\; \left(\operatorname{Finite}\left(x\right) \land \operatorname{Unit}\left(h\right)\right) \Rightarrow \operatorname{Equivalent}\left(\frac{\operatorname{kappa}\left(x + h\right) - \operatorname{kappa}\left(x\right)}{h} - \operatorname{first}\left(\operatorname{kappaJetAt}\left(x\right)\right), \frac{h \cdot \left(3 \cdot x^{2} + 2 \cdot x \cdot h - 1\right)}{\left(1 + x^{2}\right)^{2} \cdot \left(1 + \left(x + h\right)^{2}\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.kappa_secant_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula compares the secant at nonzero finite increment h with the linear jet coefficient at x. Both fidelity denominators are positive for finite rational inputs.

**Theorem 1.7 (Leibniz's rule through every degree).**

$$\forall N \in \mathbb{N},\; \forall f \in JetSeq, g \in JetSeq,\; \operatorname{EquivalentAt}\left(N, \operatorname{deriv}\left(f \cdot g\right), \operatorname{deriv}\left(f\right) \cdot g + f \cdot \operatorname{deriv}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_mul_equivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivalence through degree N requires agreement at every coefficient from zero to N inclusive. The derivative at degree N reads the coefficient in degree N + 1.

**Theorem 1.8 (The exponential differential equation).**

$$\forall a \in IntRatio,\; \operatorname{Equivalent}\left(\operatorname{deriv}\left(\operatorname{Exp}\left(a\right)\right), a \cdot \operatorname{Exp}\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient at degree n is a to the power n divided by n factorial. Setting a to one gives the unit-rate exponential equation.

**Theorem 1.9 (The cosine differential equation).**

$$\operatorname{Equivalent}\left(\operatorname{deriv}\left(Cos\right), -Sin\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_cos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cosine coefficients in even degree 2n are the alternating signs divided by (2n) factorial. The odd coefficients vanish.

**Theorem 1.10 (The sine differential equation).**

$$\operatorname{Equivalent}\left(\operatorname{deriv}\left(Sin\right), Cos\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_sin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sine coefficients in odd degree 2n + 1 are the alternating signs divided by (2n + 1) factorial. The even coefficients vanish.

**Theorem 1.11 (The exponential addition law).**

$$\forall a \in IntRatio, b \in IntRatio,\; \operatorname{Equivalent}\left(\operatorname{Exp}\left(a\right) \cdot \operatorname{Exp}\left(b\right), \operatorname{Exp}\left(a + b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.exp_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Leibniz's rule gives the rate a + b for the product. Its constant coefficient is one, which fixes the solution coefficient by coefficient.

**Theorem 1.12 (The formal exponential inverse).**

$$\forall a \in IntRatio,\; \operatorname{Finite}\left(a\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{Exp}\left(a\right) \cdot \operatorname{Exp}\left(-a\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.exp_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite parameter, adding its negative gives the zero rate. The formal exponential at the zero rate is the constant series one.

**Theorem 1.13 (The formal Pythagorean identity).**

$$\operatorname{Equivalent}\left(Cos^{2} + Sin^{2}, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cos_sq_add_sin_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the sum of the two squares vanishes by Leibniz's rule and the two trigonometric differential equations. The constant coefficient is one.

**Theorem 1.14 (The arctangent differential equation).**

$$\operatorname{Equivalent}\left(\operatorname{deriv}\left(Atan\right) \cdot \left(1 + eta^{2}\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.atan_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In degree 2n + 1, arctangent has the alternating sign divided by 2n + 1. The even coefficients vanish. After differentiation the alternating even powers cancel against their two-degree shift.

**Theorem 1.15 (The Cayley cosine differential equation).**

$$\operatorname{Equivalent}\left(\operatorname{deriv}\left(CayleyCos\right) \cdot \left(1 + eta^{2}\right), -2 \cdot CayleySin\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cayley_cos_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Cayley cosine is the formal rational function with numerator 1 - eta squared and denominator 1 + eta squared.

**Theorem 1.16 (The Cayley sine differential equation).**

$$\operatorname{Equivalent}\left(\operatorname{deriv}\left(CayleySin\right) \cdot \left(1 + eta^{2}\right), 2 \cdot CayleyCos\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cayley_sin_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Cayley sine has numerator 2 eta and the same denominator as the Cayley cosine.

**Theorem 1.17 (The Cayley system determines each truncation).**

$$\forall N \in \mathbb{N},\; \forall f \in JetSeq, g \in JetSeq,\; \left(\operatorname{Equivalent}\left(\operatorname{coeff}\left(f, 0\right), 1\right) \land \operatorname{Equivalent}\left(\operatorname{coeff}\left(g, 0\right), 0\right)\right) \Rightarrow \left(\left(\left(\forall k \in \mathbb{N},\; k < N \Rightarrow \operatorname{Equivalent}\left(\operatorname{coeff}\left(\operatorname{deriv}\left(f\right) \cdot \left(1 + eta^{2}\right), k\right), \operatorname{coeff}\left(-2 \cdot g, k\right)\right)\right) \land \left(\forall k \in \mathbb{N},\; k < N \Rightarrow \operatorname{Equivalent}\left(\operatorname{coeff}\left(\operatorname{deriv}\left(g\right) \cdot \left(1 + eta^{2}\right), k\right), \operatorname{coeff}\left(2 \cdot f, k\right)\right)\right)\right) \Rightarrow \left(\operatorname{EquivalentAt}\left(N, f, CayleyCos\right) \land \operatorname{EquivalentAt}\left(N, g, CayleySin\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cayley_unique_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The streams start at (1, 0). The equations force their coefficients through degree N to be finite. At each degree k below N, the equations determine the next coefficients by division by k + 1. Consequently both streams agree with the Cayley pair through degree N, including degree zero.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.atan_ode`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cayley_cos_ode`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cayley_sin_ode`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cayley_unique_at`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.chain_rule`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.cos_sq_add_sin_sq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_cos`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_exp`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_mul_equivAt`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.deriv_sin`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.exp_add`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.exp_inverse`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.kappa_jet`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.kappa_jet_one`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.kappa_secant_discrepancy`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.mul_inv`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaJetCalculus.var_cube`
