# Local multiplicity of polynomial radical sums

## Abstract

A finite sum of polynomial multiples of quadratic radicals is determined by a quadratic initial jet.

**Theorem 1.1 (A cutoff allowing repeated radicals and cancellation).**

$$\forall I \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(I\right)] \forall S \in I \to \operatorname{RealPowerSeries}\left(\right),\; \forall p \in I \to \operatorname{RealPolynomial}\left(\right),\; \forall A \in I \to \operatorname{RealPolynomial}\left(\right),\; \operatorname{RadicalData}\left(I, S, p, A\right) \land (\forall k \in Nat,\; k \le 3\operatorname{card}\left(I\right)^{2} \implies \operatorname{coeff}\left(k, \operatorname{RadicalSum}\left(S, A\right)\right) = 0) \implies \operatorname{RadicalSum}\left(S, A\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/RadicalMultiplicity.sum_eq_zero_of_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be any finite type, n its cardinality, p_i and A_i real polynomials, and S_i real formal power series. RadicalData means S_i squared equals p_i, the constant coefficient of S_i is nonzero, the degree of p_i is at most two, and the degree of A_i is at most n, for every i. Put Z equal to the sum of A_i S_i. If every coefficient of Z from zero through 3n squared, inclusive, is zero, then Z is the zero series. Zero polynomials, constant radicands, repeated S_i, arbitrary signs and the empty index type are allowed.

Select an independent subfamily of the summands over the real constants. Embed its series into the Laurent-series differential field; its derivative has exactly the real constants as kernel. The differential-field Wronskian criterion makes the selected Wronskian nonzero. Iterated differentiation of A times S, with S squared equal to p, gives S p to the negative v times B_v, where B_0=A and B_(v+1)=p B_v' +(1/2-v)p'B_v. The bound degree B_v<=d+2v gives Wronskian order at most l(d+2(l-1)) for a selected family of size l with coefficient degrees at most d. A nonzero constant linear combination therefore has order at most l(d+2(l-1))+l-1. With d=n and l<=n this is below 3n squared. Replacing a column by Z transfers a long initial zero jet to that determinant and contradicts its degree bound. The independent span may have dimension one, and the original summands need not be independent.

This theorem concerns formal series over the reals. Its application to actual allocation functions requires the analytic extension, coefficient correspondence and source term-count calculation in CdsoAllocationGerms. It makes no assertion about distinct real zeros or global behavior.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/RadicalMultiplicity.sum_eq_zero_of_coeff_eq_zero`
