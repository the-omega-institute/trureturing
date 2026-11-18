# Half-current modes and normal ordering

## Abstract

Local coordinate transport of the original twisted oscillator

**Theorem 1.1 (The native current under divided lowering).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_current_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_current_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At each order n, the divided power L(1)^n/n! applied to a current on any oscillator polynomial is the sum over shifts k from zero through n. Its k-th term is choose(-j-1/2,k) times the shifted current j+k applied to the divided power of order n-k. The actual inverse Gram matrix enters through the current commutator.

**Definition 1.2 (Formal divided lowering).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.loweringFlow`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.loweringFlow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The coefficient of order n is L(1)^n/n! on the original oscillator.

**Definition 1.3 (Formal conjugated current).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.transportedCurrent`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.transportedCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The coefficient of order n shifts the signed mode index by n and multiplies by choose(-j-1/2,n).

**Theorem 1.4 (Conjugation as an intertwining identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_flow_intertwines`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_flow_intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The formal lowering flow intertwines the original current with the shifted series in the endomorphisms of algebraic oscillator polynomials.

**Definition 1.5 (Creation part).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.creationPart`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.creationPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Shifts through the original negative range remain multiplication by a variable.

**Definition 1.6 (Annihilation part).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.annihilationPart`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.annihilationPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Shifts into the positive range act by the actual frequency times Gram-weighted differentiation.

**Definition 1.7 (Ordinary contraction coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.contractionScalar`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.contractionScalar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For modes p and q the sum over n from zero through q multiplies n+1/2 by the binomial coefficients at shifts p+n+1 and q-n.

**Definition 1.8 (The central contraction series).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.contraction`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.contraction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The pair contributes at order p+q+1 with the original Gram entry and the ordinary contraction coefficient.

**Theorem 1.9 (Exact central commutator).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.annihilation_creation_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.annihilation_creation_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The positive part of the transported p mode commutes through the negative part of the transported q mode with the stated central correction. The original Heisenberg relation leaves exactly opposite frequencies.

**Theorem 1.10 (Cutoff from doubled oscillator energy).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_after_energy_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_after_energy_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For a homogeneous oscillator polynomial of doubled energy z, its n-th lowering power is zero when 2n exceeds z. This uses the original L(0) spectrum and the Virasoro relation with L(1).

**Definition 1.11 (Normal ordering by partial matchings).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.normalOrder`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.normalOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The first slot remains a creator or pairs with one later slot. Removing both paired slots leaves the same rule for all remaining slots. Repeated modes occupy distinct slots.

**Theorem 1.12 (All occupations of creation words).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order_word`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At every order the normal ordering of a word on the vacuum gives the actual divided lowering power of its polynomial. Moving a positive mode through the remaining transformed word gives one term per available pairing.

**Definition 1.13 (Chosen half-coordinate scale).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.modeScale`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.modeScale` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

A signed mode j receives the chosen square root of lambda times the integer power lambda^(-j-1).

**Theorem 1.14 (Opposite modes cancel the coordinate scale).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaled_contraction_term`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaled_contraction_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Each matched term cancels the integer powers of lambda together with the square of the chosen lift, leaving eta^(p+q+1) times the two binomial factors and the frequency.

**Definition 1.15 (Normalized binomial powers).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.unitPower`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.unitPower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Coefficient n of the formal power (1-eta*u)^a is (-eta)^n choose(a,n).

**Definition 1.16 (Cauchy chamber coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.chamberCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.chamberCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

After substitution the chamber term with inner index n uses outer factor (1-eta*u)^(n-1/2) and inner factor (1-eta*v)^(-n-3/2). Only n through q contribute to u^p v^q.

**Theorem 1.17 (Chamber coefficients equal the native contraction).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.chamber_coefficient_eq_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.chamber_coefficient_eq_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Negative binomial reflection converts both chamber factors to the binomial coefficients of the actual commuting modes.

**Theorem 1.18 (Regular local Cauchy correction).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.regular_cauchy_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.regular_cauchy_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For roots b and c of 1-eta*u and 1-eta*v, the dressed Cauchy kernel minus the original kernel equals eta*(1+b*c)/(2*b*c*(b+c)^2). The rational identity holds off the diagonal and the right side extends across it wherever its denominator is nonzero.

**Definition 1.19 (Normal ordering on oscillator polynomials).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.polynomialCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.polynomialCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Expand the actual finite monomial support and evaluate the corresponding normal-ordered words with the original polynomial coefficients.

**Theorem 1.20 (Every original oscillator polynomial).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary polynomial input, every coefficient is the actual power of L(1) divided by its factorial.

**Theorem 1.21 (Finite evaluation of the lowering flow).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At any finite cutoff, the sum of the normally ordered coefficients weighted by powers of eta equals the original finite lowering sum.

**Theorem 1.22 (Both lowering factors of the original four-point kernel).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.oscillator_kernel_normal_order`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.oscillator_kernel_normal_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Replace the two divided lowering powers by their normally ordered coefficients inside the original bilinear Wick evaluation. The original indices, signs and corrected field coefficients appear at their original values.

**Theorem 1.23 (Finite cutoff on mixed oscillator energies).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.exists_lowering_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.exists_lowering_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The largest doubled energy in the finite monomial support bounds the divided lowering sum on any polynomial.

**Definition 1.24 (Diagonal scaling on the oscillator algebra).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaleOscillator`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaleOscillator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Each original generator is multiplied by its half-integral weight using the chosen lift of lambda.

**Definition 1.25 (Scaled transported current).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaledCurrent`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaledCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At order n the shift j+n receives the generalized binomial coefficient and the chosen half-integral weight of its shifted frequency.

**Theorem 1.26 (Current transport with the chosen half-coordinate lift).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaled_lowering_flow_intertwines`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaled_lowering_flow_intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Compose the lowering flow with diagonal scaling. The resulting formal series intertwines each original current with the scaled shifted expansion on the actual oscillator.

**Theorem 1.27 (Both skew-channel detector factors).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.skew_channels_normal_order`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.skew_channels_normal_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The detector in both original skew channels is evaluated by the same ordinary normal-order coefficients, through the original skew cutoffs and with the original phases and field index shifts.

The local coordinate is F(u)=lambda*u/(1-eta*u). The normalized square root of 1-eta*u has constant coefficient one, and the specified lift of lambda fixes the square root factor in the weight. The coordinate kernel uses ordinary spatial coefficients. The lowering flow uses divided powers in the coordinate parameter.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.annihilationPart`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.annihilation_creation_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.chamberCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.chamber_coefficient_eq_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.contraction`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.contractionScalar`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.creationPart`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.exists_lowering_cutoff`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.loweringFlow`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_after_energy_cutoff`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_current_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_flow_intertwines`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order_finite`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.lowering_normal_order_word`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.modeScale`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.normalOrder`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.oscillator_kernel_normal_order`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.polynomialCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.regular_cauchy_correction`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaleOscillator`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaledCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaled_contraction_term`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.scaled_lowering_flow_intertwines`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.skew_channels_normal_order`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.transportedCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport.unitPower`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset](../TwistedGround/OriginalFourMChargeCoset.md)
