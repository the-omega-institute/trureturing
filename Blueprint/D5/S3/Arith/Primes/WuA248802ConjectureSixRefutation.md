# Wu's full A248802 Conjecture 6 is false

## Abstract

An admissible overlap with House's 1759 progression refutes Wu's full Conjecture 6.

**Definition 1.1 (C1 coverage domain).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{coveredOne}\left(k\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; k = 10 \cdot m + 2)$$

*Formalization.* `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredOne` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

C1 includes every natural parameter, including zero.

**Definition 1.2 (C2 coverage domain).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{coveredTwo}\left(k\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; (k = 36 \cdot m + 16) \land (\neg (\operatorname{mod}\left(m, 5\right) = 1)))$$

*Formalization.* `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredTwo` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

C2 retains the parameter restriction m mod 5 not equal to 1.

**Definition 1.3 (C3 coverage domain).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{coveredThree}\left(k\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; (k = 84 \cdot m + 22) \land (\neg (\operatorname{mod}\left(m, 5\right) = 0)))$$

*Formalization.* `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredThree` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

C3 retains the parameter restriction m mod 5 not equal to 0.

**Definition 1.4 (C4 coverage domain).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{coveredFour}\left(k\right)) \Leftrightarrow ((\exists m \in \mathrm{Nat},\; k = 58 \cdot m + 26) \land ((\neg (\operatorname{coveredOne}\left(k\right))) \land ((\neg (\operatorname{coveredTwo}\left(k\right))) \land (\neg (\operatorname{coveredThree}\left(k\right))))))$$

*Formalization.* `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredFour` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

C4 recursively excludes C1, C2 and C3 at the same index k.

**Definition 1.5 (C5 coverage domain).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{coveredFive}\left(k\right)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; (k = 138 \cdot m + 6) \land (\neg (\operatorname{mod}\left(m, 5\right) = 2)))$$

*Formalization.* `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredFive` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

C5 retains the parameter restriction m mod 5 not equal to 2.

**Definition 1.6 (The original conditional universal claim).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (\neg (\operatorname{coveredOne}\left(44 \cdot n + 10\right))) \Rightarrow ((\neg (\operatorname{coveredTwo}\left(44 \cdot n + 10\right))) \Rightarrow ((\neg (\operatorname{coveredThree}\left(44 \cdot n + 10\right))) \Rightarrow ((\neg (\operatorname{coveredFour}\left(44 \cdot n + 10\right))) \Rightarrow ((\neg (\operatorname{coveredFive}\left(44 \cdot n + 10\right))) \Rightarrow (\operatorname{minFac}\left(2^{2^{(44 \cdot n + 10)} + 2} + 3\right) = 2383))))))$$

*Formalization.* `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.claim` (`✓ std3`).

*Citation.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

For every natural n, including zero, set k=44n+10. If none of C1 through C5 applies, the source asserts that the natural least prime factor of 2^(2^k+2)+3 is 2383. All five exclusions belong to the claim, with the earlier predicates exactly as defined above.

**Theorem 1.7 (An admissible counterexample).**

$$\neg (\operatorname{claim}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-a248802-conjecture-six-refutation` (refuted) by `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-a248802-conjecture-six-refutation","declaration_gid":"D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu; OEIS Foundation Inc. (2019). *OEIS A248802, Conjecture 6*. URL: <https://oeis.org/A248802/internal>.

*Commentary.*

The witness n=79 gives k=3486=274+292*11. Its residues modulo (10,36,84,58,138) are (6,30,42,6,36), excluding every preceding domain. The modular certificate uses 2^292=1 and 2^274=718 modulo 879, then 2^879=1 and 2^720=1756 modulo 1759. It proves 1759 divides 2^(2^3486+2)+3 without expanding the double exponential. Nat.minFac_le_of_dvd gives a(3486)<=1759<2383. Matthew House's MathOverflow answer and prior divisibility table supply the 1759 progression; the result adds the admissible intersection and the full claim's negation. No exact minimum equality or global priority is asserted.

## References

- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.claim`
- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredFive`
- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredFour`
- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredOne`
- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredThree`
- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.coveredTwo`
- Truth anchor: `D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.result`
