# The OEIS A000040 Fibonacci-Fermat Prime Characterization

## Abstract

The composite 219781 refutes Detlefs's Fibonacci-Fermat prime characterization.

**Definition 1.1 (The Fibonacci residue test).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{fibTest}\left(n\right)) \Leftrightarrow ((\operatorname{Fibonacci}\left(n\right) \bmod n = 1) \lor (\operatorname{Fibonacci}\left(n\right) \bmod n = n - 1))$$

*Formalization.* `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.fibTest` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2014). *OEIS A000040, The prime numbers*. URL: <https://oeis.org/A000040>.

*Commentary.*

For each natural n, fibTest(n) holds when the Fibonacci number F(n) has remainder one or n minus one modulo n.

**Definition 1.2 (The Fermat residue test).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{fermatTest}\left(n\right)) \Leftrightarrow (2^{n - 1} \bmod n = 1)$$

*Formalization.* `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.fermatTest` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2014). *OEIS A000040, The prime numbers*. URL: <https://oeis.org/A000040>.

*Commentary.*

For each natural n, fermatTest(n) holds when two to the power n minus one has remainder one modulo n.

**Definition 1.3 (Detlefs's proposed set).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{inDetlefsSet}\left(n\right)) \Leftrightarrow ((n = 5) \lor ((n \ne 5) \land \left((\operatorname{fibTest}\left(n\right)) \land (\operatorname{fermatTest}\left(n\right))\right)))$$

*Formalization.* `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.inDetlefsSet` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2014). *OEIS A000040, The prime numbers*. URL: <https://oeis.org/A000040>.

*Commentary.*

The proposed set contains five, together with every natural n distinct from five that satisfies both residue tests.

**Definition 1.4 (Detlefs's prime characterization).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (0 < n) \Rightarrow ((\operatorname{Prime}\left(n\right)) \Leftrightarrow (\operatorname{inDetlefsSet}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.claim` (`✓ std3`).

*Citation.* N. J. A. Sloane; Gary Detlefs (2014). *OEIS A000040, The prime numbers*. URL: <https://oeis.org/A000040>.

*Commentary.*

For every positive natural n, the characterization identifies primality exactly with membership in the proposed set.

**Theorem 1.5 (The characterization fails at 219781).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a000040-detlefs-fibonacci-fermat-prime-characterization-refutation` (refuted) by `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a000040-detlefs-fibonacci-fermat-prime-characterization-refutation","declaration_gid":"D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. J. A. Sloane; Gary Detlefs (2014). *OEIS A000040, The prime numbers*. URL: <https://oeis.org/A000040>.

*Commentary.*

The value 219781 equals 271 times 811 and is composite, while its Fibonacci remainder and its two-to-the-219780 remainder modulo 219781 are both one. Thus it belongs to the proposed set and refutes the characterization. At the degenerate boundary, the prime two is also outside the proposed set because two to the first power has remainder zero modulo two. The Fibonacci-type pseudoprime status of 219781 is prior art recorded by OEIS A094401, A093372, and A212424.

## References

- Truth anchor: `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.claim`
- Truth anchor: `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.fermatTest`
- Truth anchor: `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.fibTest`
- Truth anchor: `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.inDetlefsSet`
- Truth anchor: `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.result`
