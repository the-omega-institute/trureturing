# Actual Paired Reciprocal Tails

## Abstract

Actual Paired Reciprocal Tails

The paired summand is the sum of the positive and negative exterior squares, each divided by m^2, for all m=N+j+1>N. Its actual arithmetic symbol is negative in actual_symbol_split. The polynomial transforms are plusF=A+C(pi/4)*B, minusF=reflect(A)-C(pi/4)*reflect(B), minusG=-reflect(B), where reflect(A)(t)=A(-t).

The paired energy is functionEnergy(c,plusF,B)+functionEnergy(c,minusF,minusG). For c>=3,d>=1,d^2<=N and natDegree(A),natDegree(B)<d, the entire paired tail is summable and abs(N*sum-pairedEnergy)<=d^2*U(c)*pairedEnergy/N. Both signs retain the complete pole/Gamma correction.

The reciprocal polynomial is sum_(r<d) C(P.coeff(r)/N^(d-1-r))*X^(d-1-r). For d>=1,N>0 it has degree below d, and for natDegree(P)<d and every nonzero complex m, m^(d-1)*reciprocalPolynomial(P)(N/m)=P(m). The exact identity includes negative exterior integers.

The integral expression for pairedEnergy is the integral on [0,1] of norm(A(t)+(pi/4)*B(t))^2+norm(A(-t)-(pi/4)*B(-t))^2+mu*(norm(B(t))^2+norm(B(-t))^2).

**Definition 1.1 (pairedTerm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedTerm`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def pairedTerm (c N : ℕ) (A B : ℂ[X]) (j : ℕ) : ℝ := let m := N+j+1 let t : ℝ := (N:ℝ)/m (‖value A t-(arithmeticBoundarySymbol c (m:ℤ):ℂ)*value B t‖^2+ ‖value A (-t)-(arithmeticBoundarySymbol c (-(m:ℤ)):ℂ)*value B (-t)‖^2)/(m:ℝ)^2.

**Definition 1.2 (pairedEnergy).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedEnergy`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def pairedEnergy (c : ℕ) (A B : ℂ[X]) : ℝ := functionEnergy c (plusF A B) B+functionEnergy c (minusF A B) (minusG B).

**Theorem 1.3 (actual paired symbol enclosure).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.actual_paired_symbol_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.actual_paired_symbol_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_paired_symbol_enclosure {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N) (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) : Summable (pairedTerm c N A B) ∧ |(N:ℝ)*(∑' j : ℕ,pairedTerm c N A B j)-pairedEnergy c A B| ≤ (d:ℝ)^2*U c/(N:ℝ)*pairedEnergy c A B.

**Definition 1.4 (reciprocalPolynomial).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def reciprocalPolynomial (d N : ℕ) (P : ℂ[X]) : ℂ[X] := ∑ r ∈ Finset.range d, C (P.coeff r/(N:ℂ)^(d-1-r))*X^(d-1-r).

**Theorem 1.5 (reciprocalPolynomial degree).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma reciprocalPolynomial_degree {d N : ℕ} (hd : 1 ≤ d) (P : ℂ[X]) : (reciprocalPolynomial d N P).natDegree < d.

**Theorem 1.6 (reciprocalPolynomial exact).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem reciprocalPolynomial_exact {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N) (P : ℂ[X]) (hP : P.natDegree < d) (m : ℂ) (hm : m ≠ 0) : m^(d-1)*(reciprocalPolynomial d N P).eval ((N:ℂ)/m) = P.eval m.

**Theorem 1.7 (pairedEnergy integral).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedEnergy_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedEnergy_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma pairedEnergy_integral (c : ℕ) (A B : ℂ[X]) : pairedEnergy c A B = ∫ t in (0:ℝ)..1, (‖value A t+((Real.pi/4:ℝ):ℂ)*value B t‖^2+ ‖value A (-t)-((Real.pi/4:ℝ):ℂ)*value B (-t)‖^2+ mean c*(‖value B t‖^2+‖value B (-t)‖^2)).

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.actual_paired_symbol_enclosure`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedEnergy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedEnergy_integral`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.pairedTerm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial_degree`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualPairedReciprocal.reciprocalPolynomial_exact`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure](ActualReciprocalEnclosure.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram](WeilArithmeticCouplingParityGram.md)
