# Explicit 336 Actual Infinite Tail Bounds

## Abstract

Explicit 336 Actual Infinite Tail Bounds

For c>=3 set C336=336*c^2*(1+log(c))^3. The actual proved U(c)<=C336 is consumed by the full-symbol, paired-symbol and actual nodal column enclosures. All natural prime powers, ordered resonances and complete Gamma/pole terms remain those of the canonical suppliers.

For d>=1,d^2<=N and arbitrary complex A,B of degree below d, the paired tail is summable, abs(N*sum-H)<=epsilon*H, and (1-epsilon)*H/N<=sum<=(1+epsilon)*H/N, where epsilon=d^2*C336/N and H=pairedEnergy(c,A,B). H is nonnegative even for zero or near-cancelling input.

For finite nonempty S, d=card(S), d^2<=N, B>=0,2*B<=N and abs(n)<=B at each node, use the reciprocal polynomials of ActualNodalCoercivity.P and Q. The actual infinite paired column tail lies between (1-epsilon)*H/[pi^2*N*(1+B/N)^(2*d)] and (1+epsilon)*H/[pi^2*N*(1-B/N)^(2*d)]. The lower denominator factor 1-B/N is strictly positive.

For each eta>0 there exists N0 before every coefficient vector v, and every N>=N0 satisfies the two nodal bounds with eta. N0 depends only on c,S,B,eta. Neither the choice of cutoff nor a proof step divides by H. These are tail enclosures and do not establish dense-head positivity, RH or Robin.

**Theorem 1.1 (actual paired symbol enclosure explicit336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_symbol_enclosure_explicit336`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_symbol_enclosure_explicit336` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_paired_symbol_enclosure_explicit336 {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N) (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) : Summable (pairedTerm c N A B) ∧ |(N:ℝ)*(∑' j : ℕ, pairedTerm c N A B j)-pairedEnergy c A B| ≤ (d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ)* pairedEnergy c A B.

**Theorem 1.2 (actual paired symbol bounds explicit336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_symbol_bounds_explicit336`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_symbol_bounds_explicit336` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_paired_symbol_bounds_explicit336 {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N) (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) : let ε := (d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ) Summable (pairedTerm c N A B) ∧ (1-ε)*pairedEnergy c A B/(N:ℝ) ≤ (∑' j : ℕ, pairedTerm c N A B j) ∧ (∑' j : ℕ, pairedTerm c N A B j) ≤ (1+ε)*pairedEnergy c A B/(N:ℝ).

**Theorem 1.3 (actual paired column enclosure explicit336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_column_enclosure_explicit336`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_column_enclosure_explicit336` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_paired_column_enclosure_explicit336 {c N : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hSne : S.Nonempty) (v : ℤ → ℂ) (hNdim : S.card^2 ≤ N) {B : ℝ} (hB : 0 ≤ B) (hBN : 2*B ≤ N) (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) : let d := S.card let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v) let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v) let H := pairedEnergy c A Q let ε := (d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ) Summable (pairedColumnTerm c N S v) ∧ (1-ε)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤ (∑' j : ℕ, pairedColumnTerm c N S v j) ∧ (∑' j : ℕ, pairedColumnTerm c N S v j) ≤ (1+ε)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d)).

**Theorem 1.4 (actual paired column uniform enclosure explicit336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_column_uniform_enclosure_explicit336`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_column_uniform_enclosure_explicit336` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_paired_column_uniform_enclosure_explicit336 {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hSne : S.Nonempty) {B : ℝ} (hB : 0 ≤ B) (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) {η : ℝ} (hη : 0 < η) : ∃ N0 : ℕ, ∀ v : ℤ → ℂ, ∀ N : ℕ, N0 ≤ N → let d := S.card let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v) let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v) let H := pairedEnergy c A Q Summable (pairedColumnTerm c N S v) ∧ (1-η)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤ (∑' j : ℕ, pairedColumnTerm c N S v j) ∧ (∑' j : ℕ, pairedColumnTerm c N S v j) ≤ (1+η)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d)).

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_column_enclosure_explicit336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_column_uniform_enclosure_explicit336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_symbol_bounds_explicit336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualExplicit336.actual_paired_symbol_enclosure_explicit336`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualFunctionMetric](ActualFunctionMetric.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure](ActualNodalTailEnclosure.md)
