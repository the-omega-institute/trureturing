# Actual Reciprocal Enclosure

## Abstract

Actual Reciprocal Enclosure

The imported actual symbol retains every prime power, both ordered second-moment channels and resonant self-pairs. smoothK is the explicitSmoothK of the complete Gamma and pole estimate, chosen from the cutoff c before any polynomial or exterior mode. delta(c,m)=m^2*smoothWeight(c,m)-pi/4.

Let A(c) be the sum of the actual prime weights, D1 the actual first moment, D2 the centered offset, and mu the exact mean. Define baseAllowance=4+4*D1/sqrt(mu)+4*D2/mu and U=baseAllowance+5*K*max(1,(1+2*A+K)/mu). The energy is E(F)+mu*E(G).

For c>=3,d>=1,N>0 and polynomial degrees below d, the prime-only square tail is summable and abs(N*sum-energy)<=d^2*baseAllowance*energy/N. For d^2<=N the full square with primeSymbol+delta is summable and the same estimate holds with U. The sum always ranges over all m=N+j+1>N.

The actual suppliers prove A<=2*sqrt(c)*log(c), D1<=c*sqrt(c)*log(c)^2, D2<=c*(2*c+1)*log(c)^3 and K<=sqrt(c)*log(c). Together with mu>=1/16 these give U<=336*c^2*(1+log(c))^3 for every natural c>=3. The full-symbol enclosure consumes this bound in its infinite-tail estimate. Existing general-U results are retained. No RH, Robin inequality or dense-head positivity follows from these tail bounds.

**Definition 1.1 (smoothK).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.smoothK`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.smoothK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def smoothK (c : ℕ) : ℝ := explicitSmoothK c.

**Definition 1.2 (amplitude).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.amplitude`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.amplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def amplitude (c : ℕ) : ℝ := ∑ q ∈ primeIndices c, primeWeight q.

**Definition 1.3 (delta).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.delta`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def delta (c m : ℕ) : ℝ := (m:ℝ)^2*smoothWeight c m-Real.pi/4.

**Definition 1.4 (baseAllowance).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.baseAllowance`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.baseAllowance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def baseAllowance (c : ℕ) : ℝ := 4+4*primeFirstMoment c/Real.sqrt (mean c)+4*offset c/mean c.

**Definition 1.5 (U).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.U`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def U (c : ℕ) : ℝ := baseAllowance c + 5*smoothK c*max 1 ((1+2*amplitude c+smoothK c)/mean c).

**Definition 1.6 (functionEnergy).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.functionEnergy`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.functionEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def functionEnergy (c : ℕ) (F G : ℂ[X]) : ℝ := energy F+mean c*energy G.

**Definition 1.7 (baseTerm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.baseTerm`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.baseTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def baseTerm (c N : ℕ) (F G : ℂ[X]) (j : ℕ) : ℝ := let m := N+j+1 ‖value F ((N:ℝ)/m) + (primeSymbol c (m:ℤ):ℂ)*value G ((N:ℝ)/m)‖^2/(m:ℝ)^2.

**Definition 1.8 (fullTerm).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.fullTerm`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.fullTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lean defining declaration: def fullTerm (c N : ℕ) (F G : ℂ[X]) (j : ℕ) : ℝ := let m := N+j+1 ‖value F ((N:ℝ)/m) + ((primeSymbol c (m:ℤ)+delta c m:ℝ):ℂ)*value G ((N:ℝ)/m)‖^2/(m:ℝ)^2.

**Theorem 1.9 (functionEnergy integral).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.functionEnergy_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.functionEnergy_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma functionEnergy_integral (c : ℕ) (F G : ℂ[X]) : functionEnergy c F G = ∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2).

**Theorem 1.10 (norm square real add).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.norm_square_real_add`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.norm_square_real_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma norm_square_real_add (f g : ℂ) (p : ℝ) : ‖f+(p:ℂ)*g‖^2 = ‖f‖^2+2*p*(f*conj g).re+p^2*‖g‖^2.

**Theorem 1.11 (actual prime enclosure).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_prime_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_prime_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_prime_enclosure {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : 0 < N) (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) : Summable (baseTerm c N F G) ∧ |(N:ℝ)*(∑' j : ℕ, baseTerm c N F G j)-functionEnergy c F G| ≤ (d:ℝ)^2/(N:ℝ)*baseAllowance c*functionEnergy c F G.

**Theorem 1.12 (actual symbol split).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_symbol_split`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_symbol_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: lemma actual_symbol_split {c m : ℕ} (hm : 0 < m) : arithmeticBoundarySymbol c (m:ℤ) = -(Real.pi/4+primeSymbol c (m:ℤ)+delta c m).

**Theorem 1.13 (actual full symbol enclosure).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_full_symbol_enclosure`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_full_symbol_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_full_symbol_enclosure {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N) (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) : Summable (fullTerm c N F G) ∧ |(N:ℝ)*(∑' j : ℕ, fullTerm c N F G j)- (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2))| ≤ ((d:ℝ)^2*U c/(N:ℝ))* (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2)).

**Theorem 1.14 (U le explicit336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.U_le_explicit336`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.U_le_explicit336` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem U_le_explicit336 {c : ℕ} (hc : 3 ≤ c) : U c ≤ 336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3.

**Theorem 1.15 (actual full symbol enclosure explicit336).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_full_symbol_enclosure_explicit336`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_full_symbol_enclosure_explicit336` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Lean telescope and conclusion: theorem actual_full_symbol_enclosure_explicit336 {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : d^2 ≤ N) (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) : Summable (fullTerm c N F G) ∧ |(N:ℝ)*(∑' j : ℕ, fullTerm c N F G j)- (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2))| ≤ ((d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ))* (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2)).

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.U`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.U_le_explicit336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_full_symbol_enclosure`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_full_symbol_enclosure_explicit336`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_prime_enclosure`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.actual_symbol_split`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.amplitude`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.baseAllowance`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.baseTerm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.delta`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.fullTerm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.functionEnergy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.functionEnergy_integral`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.norm_square_real_add`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure.smoothK`
- Dependency: [D5/S3/Analytic/PolynomialReciprocalBounds](../../Analytic/PolynomialReciprocalBounds.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualFullSymbolTail](ActualFullSymbolTail.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualPrimePhaseBounds](ActualPrimePhaseBounds.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeSymbolResonance](PrimeSymbolResonance.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
