# Accumulated support approximation errors

## Abstract

A finite atomic probability on the actual unit ball gives ordinary accumulated best-term errors exceeding one.

Write M for the uniform measure on the 64 unit-ball atoms A, Iota for the actual unit-ball coercion, S for the sum of the ambient atoms, C for their real linear combination, and E(d) for the original support-tuple squared-error set. F(d) is the matrix sparse error set with K=(I+J)/128 and x_i=1/8. SupportTuple(d) consists of all tuples in the actual support, including repeated entries, and RealTuple(d) is the unrestricted real coefficient space. Let t(d)=65(64-d)/(8192(d+1)), f(n)=inf E(n+1), and T be the sum of t(d) from d=1 to 63.

**Theorem 1.1 (Integrability on the actual unit ball).**

$$Integrable\left(Iota, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.barycenter_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

M is the measure (1/64) times the sum of the 64 Dirac measures at the unit atoms a_i=(e_0+e_i)/sqrt(2), on the actual closed unit-ball subtype of Euclidean 65-space. The coercion to that Euclidean space is Bochner integrable for M. Individual Dirac integrability, finite addition and finite scalar multiplication provide the proof.

**Theorem 1.2 (The Bochner barycenter).**

$$integral\left(Iota, M\right) = \frac{1}{64} \cdot S$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.barycenter_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

The actual integral of the unit-ball coercion is (1/64) times the sum of all atoms. Finite-measure integrability is used to justify the finite-sum integral. No independently stipulated vector replaces the integral.

**Theorem 1.3 (The actual topological support).**

$$support\left(M\right) = range\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.support_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

The topological support of M equals exactly the range of the unit-ball atoms. Each atom has positive mass in every neighborhood; the finite range is closed and its complement has zero mass. The barycenter and convex hull are not added to the dictionary.

**Theorem 1.4 (The Gram scaling).**

$$\forall (c : RealTuple\left(64\right)), error\left(c\right) = quadratic\left(subtract\left(x, 8 \cdot c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.error_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

For every real coefficient vector c on the 64 atoms, the squared Hilbert error of its combination equals (x-z)-transpose K(x-z), where z_i=8c_i. This equality uses the actual integral and actual Euclidean norm; the shared coordinate and the 64 independent coordinates give the two square terms.

**Theorem 1.5 (Consolidation of repeated atoms).**

$$\forall (d : Nat), \forall (a : SupportTuple\left(d\right)), \forall (r : RealTuple\left(d\right)), \exists (c : RealTuple\left(64\right)), (card\left(support\left(c\right)\right) \le d) \land (tupleCombination\left(a, r\right) = C\left(c\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.tuple_to_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

For every natural d, every d-tuple of actual support points, and every real d-tuple of coefficients, summing coefficients over equal atom indices yields a 64-coordinate vector of support cardinality at most d with the same approximant. Repetitions, negative coefficients and cancellations are allowed.

**Theorem 1.6 (Enumeration and zero padding).**

$$\forall (d : Nat), \forall (c : RealTuple\left(64\right)), (card\left(support\left(c\right)\right) \le d) \Rightarrow \exists (a : SupportTuple\left(d\right)), \exists (r : RealTuple\left(d\right)), tupleCombination\left(a, r\right) = C\left(c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.coefficients_to_tuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

Conversely, every real coefficient vector with at most d nonzero coordinates is realized by a tuple of exactly d actual support points. Enumerate its nonzero support and pad the remaining slots by a fixed support point with coefficient zero. This also covers empty supports.

**Theorem 1.7 (Equality of the actual optimizing sets).**

$$\forall (d : Nat), E\left(d\right) = F\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.errorSet_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

For every natural d, the original support-tuple squared-error set equals the full real sparse quadratic error set. Consolidation and enumeration give both directions, and multiplication by eight is invertible and preserves nonzero supports.

**Theorem 1.8 (Attained Hilbert infima).**

$$\forall (d : Nat), ((1 \le d) \land (d \le 64)) \Rightarrow IsLeast\left(E\left(d\right), t\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.errors_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

For every d between one and 64, the original support-tuple error set has least element t(d)=65(64-d)/(8192(d+1)). Equality of the actual sets transports the all-real lower bound and its attaining optimizer.

**Theorem 1.9 (The eventual zero errors).**

$$\forall (d : Nat), (64 \le d) \Rightarrow IsLeast\left(E\left(d\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.errors_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

For every d at least 64, the actual error set has least element zero. All 64 atoms with coefficient 1/64 give the barycenter, and zero coefficients pad longer tuples. Squared norms are nonnegative.

**Theorem 1.10 (The ordinary infinite sum).**

$$HasSum\left(f, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.ordinary_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

The sequence of actual best squared errors at d=n+1 is zero for every n at least 63. It therefore HasSum T, where T is the finite sum of t(d) for d=1 through 63. This establishes ordinary convergence and uses no divergent-real-tsum fallback.

**Theorem 1.11 (The full Hilbert assertion is false).**

$$\neg Q$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ekene E. (2026). *A bound on accumulated PSD contractions, revision 2*. URL: <https://mathoverflow.net/revisions/509794/2>.

*Commentary.*

Q denotes the full original assertion: for every real Hilbert space H and probability measure on its unit ball, with v the Bochner barycenter, the squared infima of the errors over arbitrary real coefficients and exactly d points of the actual topological support, repetitions permitted, have an ordinary infinite sum at most one. The closed definition claim asserts existence of a real HasSum total with that bound, without assuming summability as an extra premise. The 64-atom witness has an integrable coercion, nonempty bounded-below error sets, attained infima and an eventual zero tail. Its ordinary total is T>1, so uniqueness of HasSum refutes Q. Ekene E., MathOverflow 509794 revision 2, CC BY-SA 4.0, supplies the original question. This is the second separately required negation in the same source event as the finite assertion.

## References

- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.barycenter_eq`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.barycenter_integrable`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.coefficients_to_tuple`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.errorSet_eq`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.error_bridge`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.errors_exact`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.errors_zero`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.ordinary_sum`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.support_eq`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.tuple_to_coefficients`
- Dependency: [D5/S3/QuadraticForms/AccumulatedSparseRefutation](../../QuadraticForms/AccumulatedSparseRefutation.md)
