# The Integer Source and Dyadic Parity of OEIS A397592

## Abstract

Integer existence and uniqueness for the literal source of A397592, together with its dyadic-neighbor parity assertion for every source solution.

The source predicate is `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.SourceA397592`. For A in Z[[X]], A_Q denotes A.map (Int.castRingHom Rat), its coefficientwise integer-to-rational image in Q[[X]]: coeff j(A_Q) is the rational image of coeff j(A) for every natural j. The sequence starts at index zero, with a(n)=coeff n(A) and a(0)=1. The operation rescale(1/m,A_Q) means A_Q(X/m). Its mth power is ordinary multiplication of formal series, with no factorial normalization or convergence premise.

**Definition 1.1 (The literal rational-rescaling source).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{SourceA397592}\left(A\right) \iff (\operatorname{constantCoeff}\left(A\right) = 1 \land (\forall m: \mathbb{N}, 0 < m \implies \sum_{j = 0}^{m - 1} \operatorname{coeff}\left(j, (\operatorname{rescale}\left(\frac{1}{m}, A_{\mathbb{Q}}\right))^{m}\right) = 2^{m - 1}))$$

*Formalization.* `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.SourceA397592` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A397592: doubled linear rows and dyadic parity*. URL: <https://oeis.org/A397592>.

*Commentary.*

The sum contains exactly the first m coefficients, at indices j=0 through m-1, for every natural m>0. The equality is in Q and the unknown series has integer coefficients. This is the NAME equation with the constant term specified by the source's ordinary generating series and offset zero.

**Theorem 1.2 (Integer well-posedness and Hanna's parity assertion).**

$$(\exists! A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{SourceA397592}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{SourceA397592}\left(A\right) \implies \forall n: \mathbb{N}, 3 < n \implies (\operatorname{Odd}\left(\operatorname{coeff}\left(n, A\right)\right) \iff (\exists k: \mathbb{N}, 1 < k \land (n = 2^{k} - 1 \lor n = 2^{k} + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397592-dyadic-parity` (proved) by `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397592-dyadic-parity","declaration_gid":"D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397592: doubled linear rows and dyadic parity*. URL: <https://oeis.org/A397592>.

*Commentary.*

The first conjunct asserts existence of an integer source and uniqueness among all integer series satisfying the literal equation. The second applies to every such series and every natural n>3. Oddness is equivalent in both directions to one of the two indices 2^k-1 and 2^k+1 for a natural k>1. The A397591 series starts at index one with zero constant term and has a different defining equation; it is not the source named here.

## References

- Truth anchor: `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.SourceA397592`
- Truth anchor: `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.SourceA397592`
- Truth anchor: `D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.result`
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](LinearExponentDyadicSupport.md)
