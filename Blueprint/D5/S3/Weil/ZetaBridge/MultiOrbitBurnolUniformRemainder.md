# Uniform Multi-Orbit Burnol Remainder

Status: Candidate source and author projection. No successful Lean compilation is claimed by this document.

The actual synthesized tests are

`f_N,a = sum_i a_i (b^{*(N+1)} * k_i)`.

Both target signs are preserved at every N. In particular the selected even channels vanish. The exact selected-orbit union contributes

`-4 sum_i m_i |a_i|^2`.

Writing the complete, absolutely convergent Weil zero sum as that contribution plus R_N(a), the module derives

`|R_N(a)| <= (1/4)^(N+1) C_basis sum_i |a_i|^2`.

The factor tends to zero independently of a. Positive integral analytic multiplicities give the target margin 4, so one finite common N makes the full form strictly negative on every nonzero coefficient vector. Reduced odd evaluation remains a right inverse, proving synthesis injective.

This closes the finite-frame remainder obligation that was previously an input to `QuantitativeMultiOrbitWeilNegativeCertificate`. It does not instantiate that older certificate for its arbitrary fixed basis; it constructs a new, jointly localized basis with proved estimates.

The valid frame is the only orbit assumption. Neither existence of off-line zeros nor a uniform estimate over all moving frames is asserted. Empty frames give the zero-dimensional case; a nonempty frame is required to extract an actual negative test.

Main declarations: `burnolSynthesis_target_union_value`, `multiOrbitBurnol_uniform_remainder`, `multiOrbitBurnol_error_tendsto_zero`, `exists_common_depth_strictly_negative`, `finite_multiOrbit_full_weil_negative_family`.
