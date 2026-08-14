# Xi Product Endpoint Limits

## Abstract

The displayed xi product form attains both endpoint values through punctured limits.

**Theorem 1.1 (Xi product form tends to one-half at zero).**

$$\lim_{s\to0, s\neq0}\frac{1}{2}\,s(s-1)\,\Lambda(s)=\frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Mellin reconstruction gives the pole clause that s times the completed-zeta reading tends to minus one at zero. Multiplication by the continuous factor one-half times s minus one yields the displayed limit.

The approach is punctured at zero. This theorem does not assert the false literal equality obtained by evaluating the raw totalized product there.

**Theorem 1.2 (Xi product form tends to one-half at one).**

$$\lim_{s\to1, s\neq1}\frac{1}{2}\,s(s-1)\,\Lambda(s)=\frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_tendsto_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Mellin reconstruction gives the pole clause that s minus one times the completed-zeta reading tends to one at one. Multiplication by the continuous factor one-half times s yields the displayed limit.

The approach is punctured at one. This theorem likewise records limiting attainment rather than literal evaluation of the raw product at the pole.

**Theorem 1.3 (Xi product form attains the frozen endpoint values).**

$$\left(\lim_{s\to0, s\neq0}\frac{1}{2}\,s(s-1)\,\Lambda(s)=\frac{1}{2} \land \lim_{s\to1, s\neq1}\frac{1}{2}\,s(s-1)\,\Lambda(s)=\frac{1}{2}\right) \land \left(\xi(0)=\frac{1}{2} \land \xi(1)=\frac{1}{2}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_attains_endpoint_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two punctured limits are paired with the frozen endpoint theorem xiReading zero equals xiReading one equals one-half. Thus continuity of the pole-removed xi reading closes exactly the two points excluded by the frozen off-endpoint product identity.

The source displays the product formula globally, but the repository's completed-zeta reading is totalized at its poles. At zero and one the raw product evaluates to zero, so the honest endpoint interpretation is the punctured-limit statement recorded here.

## References

- Truth anchor: `D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_attains_endpoint_values`
- Truth anchor: `D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_tendsto_one`
- Truth anchor: `D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_tendsto_zero`
- Dependency: [D5/S3/Analytic/CompletedZetaMellinReconstruction](../../Analytic/CompletedZetaMellinReconstruction.md)
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](XiEndpointValues.md)
