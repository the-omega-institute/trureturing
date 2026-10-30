# The 5040 time slice and its uniform Fisher law

## Abstract

The central bounded time slice for 5040 has five head modes, and the uniform five-mode law has an exact positive Fisher form.

The bounded time model uses the exponent capacities (4,2,1,1) of 5040 = 2^4 * 3^2 * 5 * 7. The head coordinate has five possible values, indexed by Fin 5. At total time four each bounded tail has exactly one compatible head. The slice has twelve complete states; five head modes does not mean five complete states.

The uniform law assigns mass 1/5 to each head mode by definition. It is not asserted to be the marginal law of uniformly sampled complete time-slice states. The Fisher form is the existing categorical bilinear form, the sum of u(s)*v(s)/p(s). The geometric conclusions below concern this explicitly chosen law; they supply no Robin inequality or implication to the Riemann hypothesis.

**Definition 1.1 (The chosen law).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.uniformLaw5040`

*Formalization.* `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.uniformLaw5040` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every s in Fin 5, uniformLaw5040(s) is the real number 1/5.

**Theorem 1.2 (Positive normalized masses).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.uniformLaw5040_mem_openSimplex`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.uniformLaw5040_mem_openSimplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every mass is strictly positive and the sum of the five masses is one.

**Theorem 1.3 (Unique head completion at the central time).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.central_5040_has_five_head_modes`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.central_5040_has_five_head_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

timeSlice5040Count(4) equals twelve. For every b in TailBox tailCapacities5040 there exists exactly one h in Fin 5 such that h.val + tailSum(b) = 4 and h.val = 4 - tailSum(b). The subtraction is natural-number subtraction. Both conclusions reuse the existing bounded time-slice maximum and tail-extension results.

**Theorem 1.4 (Exact Fisher pairing).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.fisher_uniformLaw5040`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.fisher_uniformLaw5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real functions u and v on Fin 5, fisher(uniformLaw5040,u,v) equals five times the sum of u(s)*v(s). Substituting the constant mass 1/5 in each summand proves the identity.

**Theorem 1.5 (Strict positivity in every nonzero direction).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.fisher_uniformLaw5040_pos`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.fisher_uniformLaw5040_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every u from Fin 5 to the reals, u unequal to zero implies 0 < fisher(uniformLaw5040,u,u). A nonzero coordinate gives a strictly positive summand in the sum of squares. This holds on the full five-dimensional space and hence on its tangent subspace.

**Theorem 1.6 (Combined central-slice and Fisher data).**

Lean statement: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.central_5040_five_mode_fisher_data`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.central_5040_five_mode_fisher_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjunction records timeSlice5040Count(4) = 12, membership of uniformLaw5040 in openSimplex, the Fisher pairing identity for every u and v, and strict positivity for every nonzero u. It packages the preceding results without adding an arithmetic transport theorem.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.central_5040_five_mode_fisher_data`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.central_5040_has_five_head_modes`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.fisher_uniformLaw5040`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.fisher_uniformLaw5040_pos`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.uniformLaw5040`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FiveMode5040Bridge.uniformLaw5040_mem_openSimplex`
- Dependency: [D5/S1/Ledger/BoundedTimeSlice](../../Ledger/BoundedTimeSlice.md)
- Dependency: [D5/S1/Words/AdmissibleWords/FiveModeFisherMetric](FiveModeFisherMetric.md)
