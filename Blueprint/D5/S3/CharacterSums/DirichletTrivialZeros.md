# Simple parity zeros and the completed divisor

## Abstract

The complete Dirichlet zero divisor

Let χ be a complex Dirichlet character of positive modulus q. Its parity a is zero when χ is even, and one otherwise. The ordinary and completed L-functions use the Mathlib continuations, while completion(χ,s) includes the nonvanishing factor exp(s log(q)/2).

**Definition 1.1 (The parity lattice).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall n \in \operatorname{Naturals}\left(\right),\; \operatorname{trivialPoint}\left(chi, n\right) = \operatorname{sub}\left(\operatorname{neg}\left(\operatorname{parity}\left(chi\right)\right), \operatorname{mul}\left(2, \operatorname{natToComplex}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletTrivialZeros.trivialPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here n is any natural number and a is the parity. The even lattice includes zero; the odd lattice begins at minus one.

**Definition 1.2 (completion).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall s \in \operatorname{Complexes}\left(\right),\; \operatorname{completion}\left(chi, s\right) = \operatorname{mul}\left(\operatorname{complexExp}\left(\operatorname{mul}\left(\operatorname{realToComplex}\left(\operatorname{div}\left(\operatorname{log}\left(q\right), 2\right)\right), s\right)\right), \operatorname{completedLFunction}\left(chi, s\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletTrivialZeros.completion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fχ(s) = exp(s log(q)/2) completedLFunction(χ,s). The exponential is never zero, so this normalization preserves the zero divisor.

**Definition 1.3 (gammaConstant).**

$$\operatorname{gammaConstant}\left(\right) = \operatorname{max}\left(1, \operatorname{RealGamma}\left(\operatorname{quarter}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletTrivialZeros.gammaConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant A = max(1,Γ(1/4)) controls Gamma values near zero.

**Definition 1.4 (growthConstant).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \operatorname{growthConstant}\left(q\right) = \operatorname{max}\left(\operatorname{add}\left(\operatorname{log}\left(\operatorname{mul}\left(\operatorname{gammaConstant}\left(\right), \operatorname{totient}\left(q\right)\right)\right), \operatorname{add}\left(\operatorname{div}\left(\operatorname{log}\left(q\right), 2\right), \operatorname{mul}\left(2, \operatorname{log}\left(2\right)\right)\right)\right), 3\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletTrivialZeros.growthConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G(q) = max(log(A totient(q))+log(q)/2+2 log(2),3).

**Theorem 1.5 (Gamma upper bounds).**

$$\operatorname{and}\left(\forall z \in \operatorname{Complexes}\left(\right),\; \operatorname{implies}\left(\operatorname{lt}\left(0, \operatorname{re}\left(z\right)\right), \operatorname{le}\left(\operatorname{norm}\left(\operatorname{Gamma}\left(z\right)\right), \operatorname{RealGamma}\left(\operatorname{re}\left(z\right)\right)\right)\right), \operatorname{and}\left(\forall u \in \operatorname{Reals}\left(\right),\; \operatorname{implies}\left(\operatorname{le}\left(\operatorname{div}\left(1, 4\right), u\right), \operatorname{or}\left(\operatorname{le}\left(\operatorname{RealGamma}\left(u\right), \operatorname{RealGamma}\left(\operatorname{quarter}\left(\right)\right)\right), \operatorname{lt}\left(\operatorname{RealGamma}\left(u\right), \operatorname{exp}\left(\operatorname{mul}\left(\operatorname{add}\left(u, 1\right), \operatorname{log}\left(\operatorname{add}\left(u, 1\right)\right)\right)\right)\right)\right)\right), \forall u \in \operatorname{Reals}\left(\right),\; \operatorname{implies}\left(\operatorname{le}\left(\operatorname{div}\left(1, 4\right), u\right), \operatorname{le}\left(\operatorname{RealGamma}\left(u\right), \operatorname{max}\left(\operatorname{RealGamma}\left(\operatorname{quarter}\left(\right)\right), \operatorname{factorial}\left(\operatorname{natSub}\left(\operatorname{ceilingNat}\left(u\right), 1\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletTrivialZeros.gamma_growth_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re z > 0, |Γ(z)| ≤ Γ(Re z). For u ≥ 1/4, the real Gamma value is at most max(Γ(1/4),(ceilNat(u)-1)!), and is either at most Γ(1/4) or strictly below exp((u+1)log(u+1)). The factorial and exponential conclusions are both retained; the factorial subtraction is natural subtraction.

**Theorem 1.6 (Explicit, logarithmic and power growth).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \operatorname{implies}\left(\operatorname{notPrincipal}\left(chi\right), \forall s \in \operatorname{Complexes}\left(\right),\; \operatorname{implies}\left(\operatorname{or}\left(\operatorname{le}\left(\operatorname{div}\left(1, 2\right), \operatorname{re}\left(s\right)\right), \operatorname{primitive}\left(chi\right)\right), \operatorname{and}\left(\operatorname{lt}\left(\operatorname{norm}\left(\operatorname{completion}\left(chi, s\right)\right), \operatorname{mul}\left(\operatorname{gammaConstant}\left(\right), \operatorname{totient}\left(q\right), \operatorname{add}\left(1, \operatorname{norm}\left(s\right)\right), \operatorname{exp}\left(\operatorname{add}\left(\operatorname{mul}\left(\operatorname{div}\left(\operatorname{log}\left(q\right), 2\right), \operatorname{add}\left(1, \operatorname{norm}\left(s\right)\right)\right), \operatorname{mul}\left(\operatorname{div}\left(\operatorname{add}\left(\operatorname{norm}\left(s\right), 4\right), 2\right), \operatorname{log}\left(\operatorname{div}\left(\operatorname{add}\left(\operatorname{norm}\left(s\right), 4\right), 2\right)\right)\right)\right)\right)\right)\right), \operatorname{and}\left(\operatorname{lt}\left(\operatorname{norm}\left(\operatorname{completion}\left(chi, s\right)\right), \operatorname{exp}\left(\operatorname{mul}\left(\operatorname{growthConstant}\left(q\right), \operatorname{add}\left(1, \operatorname{norm}\left(s\right)\right), \operatorname{add}\left(1, \operatorname{log}\left(\operatorname{add}\left(1, \operatorname{norm}\left(s\right)\right)\right)\right)\right)\right)\right), \operatorname{lt}\left(\operatorname{norm}\left(\operatorname{completion}\left(chi, s\right)\right), \operatorname{exp}\left(\operatorname{mul}\left(3, \operatorname{growthConstant}\left(q\right), \operatorname{power}\left(\operatorname{add}\left(1, \operatorname{norm}\left(s\right)\right), \operatorname{div}\left(3, 2\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletTrivialZeros.completion_power_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For χ nonprincipal, the three displayed bounds hold whenever Re s ≥ 1/2 or χ is primitive. The explicit Gamma prefactor bound and exp(G(q)(1+|s|)(1+log(1+|s|))) are retained alongside the power bound exp(3G(q)(1+|s|)^(3/2)) used by Hadamard analysis. Primitivity supplies reflection on the left half-plane.

**Theorem 1.7 (The open strip).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \operatorname{implies}\left(\operatorname{primitive}\left(chi\right), \forall rho \in \operatorname{Complexes}\left(\right),\; \operatorname{implies}\left(\operatorname{completion}\left(chi, rho\right) = 0, \operatorname{and}\left(\operatorname{lt}\left(0, \operatorname{re}\left(rho\right)\right), \operatorname{lt}\left(\operatorname{re}\left(rho\right), 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletTrivialZeros.completion_zero_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every zero of a primitive completion has 0 < Re ρ < 1. The Euler product excludes Re ρ ≥ 1 and the functional equation excludes Re ρ ≤ 0. Nonprincipality is not assumed here.

**Theorem 1.8 (The vertical resolvent identity).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \operatorname{implies}\left(\operatorname{primitiveNonprincipal}\left(chi\right), \forall sigma \in \operatorname{Reals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{implies}\left(\operatorname{ne}\left(\operatorname{apply}\left(\operatorname{completion}\left(chi\right), \operatorname{add}\left(\operatorname{realToComplex}\left(sigma\right), \operatorname{mul}\left(\operatorname{realToComplex}\left(t\right), \operatorname{imaginaryUnit}\left(\right)\right)\right)\right), 0\right), \operatorname{HasSum}\left((fun (rho: \operatorname{zeroSet}\left(\operatorname{completion}\left(chi\right)\right)) \mapsto \operatorname{div}\left(\operatorname{mul}\left(\operatorname{analyticOrderNatAt}\left(\operatorname{completion}\left(chi\right), rho\right), \operatorname{sub}\left(sigma, \operatorname{re}\left(rho\right)\right)\right), \operatorname{add}\left(\operatorname{power}\left(\operatorname{sub}\left(sigma, \operatorname{re}\left(rho\right)\right), 2\right), \operatorname{power}\left(\operatorname{sub}\left(t, \operatorname{im}\left(rho\right)\right), 2\right)\right)\right)), \operatorname{re}\left(\operatorname{logDeriv}\left(\operatorname{completion}\left(chi\right), \operatorname{add}\left(\operatorname{realToComplex}\left(sigma\right), \operatorname{mul}\left(\operatorname{realToComplex}\left(t\right), \operatorname{imaginaryUnit}\left(\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletTrivialZeros.completion_vertical_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For primitive nonprincipal χ and Fχ(σ+it) ≠ 0, the real logarithmic derivative at σ+it is the absolutely convergent sum of mρ(σ-Re ρ)/|σ+it-ρ|². The same-character reflection ρ ↦ 1-conj(ρ) preserves orders. Pairing the existing two-point Hadamard identity removes the undetermined constant. The inverse-square zero sum and the strip bound |σ-Re ρ| ≤ |σ|+1 give absolute convergence at every nonzero center.

**Theorem 1.9 (Conductor, Gamma and arithmetic logarithmic derivatives).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall s \in \operatorname{Complexes}\left(\right),\; \operatorname{implies}\left(\operatorname{and}\left(\operatorname{lt}\left(0, \operatorname{re}\left(s\right)\right), \operatorname{and}\left(\operatorname{ne}\left(\operatorname{apply}\left(\operatorname{LFunction}\left(chi\right), s\right), 0\right), \operatorname{or}\left(\operatorname{ne}\left(s, 1\right), \operatorname{notPrincipal}\left(chi\right)\right)\right)\right), \operatorname{logDeriv}\left(\operatorname{completion}\left(chi\right), s\right) = \operatorname{add}\left(\operatorname{realToComplex}\left(\operatorname{div}\left(\operatorname{sub}\left(\operatorname{log}\left(q\right), \operatorname{log}\left(\operatorname{pi}\left(\right)\right)\right), 2\right)\right), \operatorname{add}\left(\operatorname{mul}\left(\operatorname{half}\left(\right), \operatorname{digamma}\left(\operatorname{div}\left(\operatorname{add}\left(s, \operatorname{parity}\left(chi\right)\right), 2\right)\right)\right), \operatorname{logDeriv}\left(\operatorname{LFunction}\left(chi\right), s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletTrivialZeros.completion_logDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re s > 0, Lχ(s) ≠ 0 and (s ≠ 1 or χ nonprincipal), the normalized logarithmic derivative is (log(q)-log(π))/2 plus half the digamma at (s+a)/2 plus Lχ′/Lχ(s), where a is the parity.

Gamma estimates give the growth bounds, while the functional equation and half-plane nonvanishing place completed zeros in the open strip. The two-point Hadamard identity and reflection yield the resolvent formula. Negative-integer derivative nonvanishing gives the simple Gamma lattice multiplicities used in the divisor identity.

**Theorem 1.10 (Exact zero set and multiplicity).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall s \in \operatorname{Complexes}\left(\right),\; \operatorname{implies}\left(\operatorname{and}\left(\operatorname{or}\left(\operatorname{ne}\left(s, 0\right), \operatorname{ne}\left(q, 1\right)\right), \operatorname{or}\left(\operatorname{ne}\left(s, 1\right), \operatorname{notPrincipal}\left(chi\right)\right)\right), \operatorname{and}\left(\operatorname{iff}\left(\operatorname{apply}\left(\operatorname{LFunction}\left(chi\right), s\right) = 0, \operatorname{or}\left(\operatorname{apply}\left(\operatorname{completedLFunction}\left(chi\right), s\right) = 0, \operatorname{existsNatural}\left(\operatorname{equalTrivialPoint}\left(chi, s\right)\right)\right)\right), \operatorname{analyticOrderAt}\left(\operatorname{LFunction}\left(chi\right), s\right) = \operatorname{add}\left(\operatorname{analyticOrderAt}\left(\operatorname{completedLFunction}\left(chi\right), s\right), \operatorname{ifThenElse}\left(\operatorname{existsNatural}\left(\operatorname{equalTrivialPoint}\left(chi, s\right)\right), 1, 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletTrivialZeros.LFunction_zero_divisor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex s with (s ≠ 0 or q ≠ 1) and (s ≠ 1 or χ nonprincipal), L(s,χ) vanishes exactly when the completed L-function vanishes or s = -a-2n for some n ≥ 0. Its analytic order equals the completed analytic order plus one on that lattice, and equals the completed order elsewhere. Analytic orders take values in the extended natural numbers.

Write H(z) = 1/Γ(z). The global recurrence H(z) = z H(z+1) proves H′(0) = 1, and at negative integers gives H′(-n-1) = (-n-1)H′(-n). Thus every reciprocal Gamma zero is simple. The nonvanishing exponential factor in ΓR and its affine argument preserve those orders. Multiply the completed function by the reciprocal parity Gamma factor near each regular center to obtain the asserted zero set and additive order formula. Both local exceptions hold everywhere for nonprincipal characters.

Primitivity is unnecessary for this identity. For primitive characters, a separate nonvanishing theorem for the completed function on Re s ≤ 0 makes the lattice and completed zero sets disjoint. Without that theorem this result allows their multiplicities to add at common zeros. It supplies the divisor correspondence, and asserts no zero-free rectangle.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.LFunction_zero_divisor`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.completion`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.completion_logDeriv`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.completion_power_growth`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.completion_vertical_resolvent`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.completion_zero_strip`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.gammaConstant`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.gamma_growth_bounds`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.growthConstant`
- Truth anchor: `D5/S3/CharacterSums/DirichletTrivialZeros.trivialPoint`
- Dependency: [D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds](../Analytic/Asymptotics/GammaVerticalReciprocalBounds.md)
- Dependency: [D5/S3/Analytic/Resolvent/EntireLogDerivPowers](../Analytic/Resolvent/EntireLogDerivPowers.md)
- Dependency: [D5/S3/CharacterSums/NonprincipalCharacterGrowth](NonprincipalCharacterGrowth.md)
- Dependency: [D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit](../Weil/ZetaGamma/HadamardTruncatedBinomialLimit.md)
