# Hidden Field Response

## Abstract

Exact nonresonant hidden-field elimination and its leading-order coefficient companions.

**Lemma 1.1 (Solve the hidden field).**

$$\forall Oh \in \mathbb{R}, ch \in \mathbb{R}, kSq \in \mathbb{R}, omega \in \mathbb{R}, lam \in \mathbb{R}, q \in \mathbb{R}, r \in \mathbb{R},\; (\operatorname{hiddenDen}\left(Oh, ch, kSq, omega\right) \neq 0 \land lam \cdot q + \operatorname{hiddenDen}\left(Oh, ch, kSq, omega\right) \cdot r = 0) \Rightarrow r = -{\frac{lam}{\operatorname{hiddenDen}\left(Oh, ch, kSq, omega\right)}} \cdot q$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/HiddenFieldResponse.hidden_field_solve_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second frequency-domain Euler-Lagrange equation is an explicit premise. Its nonzero hidden coefficient permits division while retaining the full frequency and squared-wave-number dependence. The variational and Fourier steps leading to that equation are outside this formalization.

**Theorem 1.2 (Exact inverse response coefficient).**

$$\forall O0 \in \mathbb{R}, Oh \in \mathbb{R}, c0 \in \mathbb{R}, ch \in \mathbb{R}, kSq \in \mathbb{R}, omega \in \mathbb{R}, lam \in \mathbb{R}, q \in \mathbb{R}, r \in \mathbb{R},\; (\operatorname{hiddenDen}\left(Oh, ch, kSq, omega\right) \neq 0 \land lam \cdot q + \operatorname{hiddenDen}\left(Oh, ch, kSq, omega\right) \cdot r = 0) \Rightarrow \left({O0}^{2} + {c0}^{2} \cdot kSq - {omega}^{2}\right) \cdot q + lam \cdot r = \left({O0}^{2} + {c0}^{2} \cdot kSq - {omega}^{2} - \frac{{lam}^{2}}{\operatorname{hiddenDen}\left(Oh, ch, kSq, omega\right)}\right) \cdot q$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/HiddenFieldResponse.hidden_field_schur_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of hidden_field_solve_eq into the visible equation identifies the exact inverse response as the coefficient multiplying q. The identity also holds at q = 0; no cancellation by the visible amplitude is used.

**Lemma 1.3 (Companion: squared-speed shift).**

$$\forall c0 \in \mathbb{R}, ch \in \mathbb{R}, lam \in \mathbb{R}, Oh \in \mathbb{R},\; \operatorname{cEffSq}\left(c0, ch, lam, Oh\right) - {c0}^{2} = \frac{\operatorname{inertiaCorrection}\left(lam, Oh\right)}{\operatorname{kineticCoeff}\left(lam, Oh\right)} \cdot \left({ch}^{2} - {c0}^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/HiddenFieldResponse.c_eff_sq_sub_bare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift is a nonnegative mixing weight times the difference of the two squared speeds. In particular, zero coupling gives zero shift.

**Lemma 1.4 (Companion: squared-speed interval).**

$$\forall c0 \in \mathbb{R}, ch \in \mathbb{R}, lam \in \mathbb{R}, Oh \in \mathbb{R},\; \operatorname{min}\left({c0}^{2}, {ch}^{2}\right) \leq \operatorname{cEffSq}\left(c0, ch, lam, Oh\right) \land \operatorname{cEffSq}\left(c0, ch, lam, Oh\right) \leq \operatorname{max}\left({c0}^{2}, {ch}^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/HiddenFieldResponse.c_eff_sq_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weights are nonnegative and sum to one, placing the coefficient between the two squared speeds.

**Lemma 1.5 (Companion: characteristic locus).**

$$\forall c0 \in \mathbb{R}, ch \in \mathbb{R}, lam \in \mathbb{R}, Oh \in \mathbb{R}, kSq \in \mathbb{R}, omega \in \mathbb{R},\; \operatorname{principalSymbol}\left(c0, ch, lam, Oh, kSq, omega\right) = 0 \iff {omega}^{2} = \operatorname{cEffSq}\left(c0, ch, lam, Oh\right) \cdot kSq$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/HiddenFieldResponse.principal_symbol_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence rewrites the zero set of the normalized massless principal symbol as the leading-order dispersion relation.

The source's physical model has positive gaps and a positive zero-momentum restoring matrix. The coefficient interpretation requires its low-frequency window; the total real expressions at a zero hidden gap carry no such claim. No controlled expansion remainder or limiting PDE is certified here.

The source does not resolve hidden resonance in this elimination. The explicit nonzero-denominator hypothesis remains; totalized division supplies no physical response at resonance. Changing the parameters can change the effective speed, so there is no universal constant or identification with the full signal front.

The parameter lam is solely the field coupling and is not identified with a resource price. This quadratic classical calculation provides no Born rule, quantum state, or thermal fluctuation distribution.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/HiddenFieldResponse.c_eff_sq_bounds`
- Truth anchor: `D5/S3/Observer/BlockStructure/HiddenFieldResponse.c_eff_sq_sub_bare`
- Truth anchor: `D5/S3/Observer/BlockStructure/HiddenFieldResponse.hidden_field_schur_response`
- Truth anchor: `D5/S3/Observer/BlockStructure/HiddenFieldResponse.hidden_field_solve_eq`
- Truth anchor: `D5/S3/Observer/BlockStructure/HiddenFieldResponse.principal_symbol_eq_zero_iff`
