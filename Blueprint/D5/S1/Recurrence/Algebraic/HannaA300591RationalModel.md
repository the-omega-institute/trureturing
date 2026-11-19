# The rational model of Hanna A300591

## Abstract

The normalized rational ordinary series and its exponential companion are unique. Its ordinary coefficients are integers in every degree, and every positive-index coefficient is an integer multiple of its index.

**Definition 1.1 (Formal scalar exponential).**

$$\forall t: \mathbb{Q}, \forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{expSeries}\left(t, F\right) = \operatorname{subst}\left(\operatorname{C}\left(t\right) \cdot F, \operatorname{exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.expSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is substitution into the formal exponential over Q. The first argument of PowerSeries.subst is the inner series. When the inner series has constant coefficient zero, this is exp(t F).

**Definition 1.2 (The original ordinary-series equation).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \iff (\operatorname{constantCoeff}\left(F\right) = 0 \land \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{2}, F\right)\right) = ((n: \mathbb{Q}))^{2} \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(((n: \mathbb{Q}))^{2}, F\right)\right)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.IsSource` (`✓ std3`).

*Citation.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

OEIS A300591 NAME gives [x^n]exp(n^2 A)=n^2[x^(n-1)]exp(n^2 A) for every n>=1. Its OFFSET starts at one. The normalized extension has constant coefficient zero. Every coefficient here is an ordinary coefficient, and the ambient coefficient field is Q. Integrality is not a hypothesis.

**Theorem 1.3 (Unique rational normalized triangular source).**

$$\forall lam: \operatorname{Function}\left(\mathbb{N}, \mathbb{Q}\right), \forall mu: \operatorname{Function}\left(\mathbb{N}, \mathbb{Q}\right), (\forall n: \mathbb{N}, (1 \le n) \implies (\neg(lam\left(n\right) = 0))) \implies (\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(F\right) = 0 \land \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(lam\left(n\right), F\right)\right) = mu\left(n\right) \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(lam\left(n\right), F\right)\right))) \land \forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{constantCoeff}\left(G\right) = 0 \land \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(lam\left(n\right), G\right)\right) = mu\left(n\right) \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(lam\left(n\right), G\right)\right)))) \implies (G = F))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.triangular_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

The functions lam and mu are arbitrary rational-valued functions on the natural numbers, and lam(n) is nonzero for every n>=1. A degree-n change of the exponent changes the degree-n exponential coefficient by lam(n) times that change and preserves all lower coefficients. The derivative recurrence and coefficient agreement give this residual identity. PowerSeriesNormalizedContraction.exists_unique_fixed then constructs the unique normalized solution over Q. Taking lam(n)=mu(n)=n^2 gives the original A300591 source, before any arithmetic assertion. No integral ambient series, coefficient cutoff or positivity premise is used. The same triangular theorem with lam(n)=mu(n)=n^3 gives the rational characterization used by HannaA300595Integrality.

**Theorem 1.4 (Local quotient integrality at index primes).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies (\forall n: \mathbb{N}, (2 \le n) \implies (\forall p: \mathbb{N}, (\operatorname{Prime}\left(p\right)) \implies ((\operatorname{Dvd}\left(p, n\right)) \implies ((\forall j: \mathbb{N}, (j < n) \implies (\operatorname{IsRIntegralRat}\left(p, \operatorname{coeff}\left(j, F\right)\right))) \implies (\operatorname{IsRIntegralRat}\left(p, \frac{\operatorname{coeff}\left(n, F\right)}{(n: \mathbb{Q})}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_local_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

For every rational source F, every n>=2, and every prime p dividing n, local integrality of the strict prefix alone implies that [x^n]F/n has denominator coprime to p. The proof truncates before degree n. For h=v_p(t)>=1, the degree-(n-1) exponential coefficient has valuation at least h, and the degree-n coefficient of the strict prefix has valuation at least 2h-1. These bounds use v_p(j!)<j and the vanishing of the zero-th and first power contributions at degree n. The original equation then gives v_p([x^n]F)>=h-1 for a nonzero coefficient. With t=n^2, this is enough for the quotient because 2v_p(n)-1>=v_p(n). Zero coefficients are handled separately. The same bound is used for every prime, including two; no stronger odd-prime estimate is asserted. This result assumes no integrality of the next coefficient and uses no signed-counting premise.

**Theorem 1.5 (The precise possible first denominator obstruction).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies (\forall n: \mathbb{N}, (\forall j: \mathbb{N}, (j < n) \implies (\exists z: \mathbb{Z}, \operatorname{coeff}\left(j, F\right) = (z: \mathbb{Q}))) \implies ((\neg(\exists z: \mathbb{Z}, \operatorname{coeff}\left(n, F\right) = (z: \mathbb{Q}))) \implies (2 \le n \land \exists p: \mathbb{N}, \operatorname{Prime}\left(p\right) \land \left(p < n \land \left(\neg(\operatorname{Dvd}\left(p, n\right)) \land \operatorname{Dvd}\left(p, \operatorname{den}\left(\operatorname{coeff}\left(n, F\right)\right)\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_denominator_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

If every coefficient before degree n is an integer and the coefficient at degree n is not, then n>=2 and its reduced denominator has a prime divisor p<n with p not dividing n. The constant coefficient is zero and the degree-one source equation forces [x]F=1. Index primes are excluded by source_local_quotient. For p>n, every factorial denominator in the finite exponential coefficient formula is a p-unit, so the strict prefix and the degree equation give local integrality directly. The theorem locates a possible obstruction; it does not exclude the remaining primes p<n coprime to n.

**Theorem 1.6 (Ordinary integrality implies integer divisibility).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies ((\forall r: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(r, F\right) = (z: \mathbb{Q})) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\exists q: \mathbb{Z}, \operatorname{coeff}\left(n, F\right) = (n: \mathbb{Q}) \cdot (q: \mathbb{Q}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_divisible_of_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

For a source F with every ordinary coefficient integral, every positive coefficient equals n times an integer. At primes dividing n, the proof uses source_local_quotient and the actual strict prefix. At other primes, division by n preserves local integrality of the integer coefficient. The existing integral_of_local theorem supplies an integer witness for the quotient. Degree one and the auxiliary quotient's zero slot are handled separately. This theorem has an explicit integrality premise; source_integral_and_divisible discharges it for every source.

**Theorem 1.7 (Ordinary integrality and positive-index divisibility).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies (\forall r: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(r, F\right) = (z: \mathbb{Q}) \land \forall n: \mathbb{N}, (1 \le n) \implies (\exists q: \mathbb{Z}, \operatorname{coeff}\left(n, F\right) = (n: \mathbb{Q}) \cdot (q: \mathbb{Q})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_integral_and_divisible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

For every rational source F, all ordinary coefficients, including degree zero, are integers, and [x^n]F=n q_n with q_n in Z for every n>=1. Strong induction uses the actual integral strict prefix to choose integer colors. Its polynomial agrees with F below the current degree. The existing exponential agreement and residual identities transfer every lower source equation and identify the current residual with -n^2[x^n]F. The signed assembly/Sylow theorem makes this residual locally integral at every prime coprime to n. source_denominator_obstruction and source_local_quotient exclude all remaining denominator primes, completing ordinary integrality. The existing source_divisible_of_integral then applies without an extra premise. Applying triangular_exists_unique with lam(n)=mu(n)=n^2 identifies the unique rational ordinary source, so this series has both arithmetic properties. No factorial-rescaled coefficient convention or finite cutoff is substituted, and the A300598 quotient is used only for n>=1.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.IsSource`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.expSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_denominator_obstruction`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_divisible_of_integral`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_integral_and_divisible`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.source_local_quotient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.triangular_exists_unique`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA300591AssemblyCoefficients](HannaA300591AssemblyCoefficients.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
