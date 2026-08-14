# Complex Golden Displacement Euler Product

## Abstract

The frozen displacement surface lifts to complex parameters and contains the convergent golden Euler germ as its conjugate section.

**Theorem 1.1 (The complex term has the frozen real norm).**

$$\forall s, w\in \mathbb{C}, \forall n\in \mathbb{N}, \lvert D^{C}_{s,w}(n)\rvert = D_{\operatorname{Re}{s},\operatorname{Re}{w}}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive natural bases have zero complex argument, so Mathlib's cpow norm formula removes both imaginary exponent components. The resulting real powers are exactly the already frozen displacement term; the zero index agrees by definition.

**Theorem 1.2 (The complex term is multiplicative on coprime factors).**

$$\forall s, w\in \mathbb{C}, \forall m, n\in \mathbb{N}, \gcd{m,n} = 1 \implies D^{C}_{s,w}(mn) = D^{C}_{s,w}(m) \cdot D^{C}_{s,w}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen hidden product splits on coprime inputs. Mathlib's natural-cast cpow multiplication law splits each positive-base complex power, and the zero cases reduce to the forced coprime unit exactly as in the real displacement surface.

**Theorem 1.3 (The complex displacement series converges absolutely).**

$$\forall s, w\in \mathbb{C}, 0 \leq \operatorname{Re}{s} \land 1 < \operatorname{Re}{s+w} \implies \sum_{n\in \mathbb{N}}\lvert D^{C}_{s,w}(n)\rvert < \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact norm theorem turns the complex absolute-value series into the nonnegative frozen real displacement series at the two real parts. Its established summability therefore supplies convergence with no new analytic estimate.

**Theorem 1.4 (The complex displacement surface has an Euler product).**

$$\forall s, w\in \mathbb{C}, 0 \leq \operatorname{Re}{s} \land 1 < \operatorname{Re}{s+w} \implies \prod_{p \text{prime}}(\sum_{e\in \mathbb{N}}(p^{-s})^{\operatorname{start}{e}} \cdot (p^{-w})^{e}) = \sum_{n\in \mathbb{N}}D^{C}_{s,w}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.complex_displacement_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned Mathlib Euler-product theorem consumes the unit value, zero value, coprime multiplicativity, and absolute summability of the complex term. Its prime-power factors are then rewritten to the displayed Hecke-Mahler monomials.

**Theorem 1.5 (The germ exponent is the conjugate-corrected substitution start).**

$$\forall e\in \mathbb{N}, o5Beta{e} = \operatorname{start}{e} - e \cdot \psi $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.o5_beta_eq_substitution_start_sub_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public Beatty formula identifies a substitution start with the floor of (e+1) times the golden ratio minus one. Substitution into o5Beta and the identity one minus the golden ratio equals its conjugate give the equality.

**Theorem 1.6 (Prime powers restrict to golden Euler germ monomials).**

$$\forall s\in \mathbb{C}, \forall p, e\in \mathbb{N}, p \text{prime} \implies D^{C}_{s,-\psi \cdot s}(p^{e}) = p^{-s \cdot o5Beta{e}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_prime_pow_germ_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the conjugate section, the two prime-power exponents combine by cpow addition. The beta/start identity reduces their sum to minus s times o5Beta e, giving the local golden Euler germ term on every prime power.

**Theorem 1.7 (The convergent golden germ is a displacement section).**

$$\forall s\in \mathbb{C}, 1 < \varphi \cdot \operatorname{Re}{s} \implies \prod_{p \text{prime}}(\sum_{e\in \mathbb{N}}p^{-s \cdot o5Beta{e}}) = \sum_{n\in \mathbb{N}}D^{C}_{s,-\psi \cdot s}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.complex_displacement_germ_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The section w = -psi s has real convergence exponent phi times Re(s). Under the strict threshold greater than one, the complex displacement Euler product therefore converges and its local prime terms rewrite to the o5Beta germ.

## References

- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.complex_displacement_euler_product`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.complex_displacement_germ_section`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_mul_of_coprime`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_norm`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_prime_pow_germ_section`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.dterm_c_summable`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct.o5_beta_eq_substitution_start_sub_conjugate`
- Dependency: [D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct](../../../S1/Deficit/Displacement/GoldenDisplacementEulerProduct.md)
