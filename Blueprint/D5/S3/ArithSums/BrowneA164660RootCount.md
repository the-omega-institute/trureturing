# Arbitrary-power root counts and translated floor products

## Abstract

Every window of n consecutive integers contains n/D_r(n) roots of k^r ≡ 0 (mod n), so Browne's floor product extends to all exponents and translates.

For positive n and r write n=∏p^(e_p). These statements are Proposition 3 of H. Ma and W. Zhang on A. Browne's final formula for OEIS A164660; the square, cube and fourth-power counts are OEIS A000188, A000189 and A000190.

**Definition 1.1 (The ceiling-exponent divisor).**

Lean statement: `D5/S3/ArithSums/BrowneA164660RootCount.D`

*Formalization.* `D5/S3/ArithSums/BrowneA164660RootCount.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products*. DOI: [10.5281/zenodo.23884883](https://doi.org/10.5281/zenodo.23884883). URL: <https://doi.org/10.5281/zenodo.23884883>.

*Commentary.*

D_r(n)=∏_{p∣n} p^⌈e_p/r⌉, built from the ceiling exponents (e_p+r−1)/r.

**Definition 1.2 (The root count).**

Lean statement: `D5/S3/ArithSums/BrowneA164660RootCount.C`

*Formalization.* `D5/S3/ArithSums/BrowneA164660RootCount.C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products*. DOI: [10.5281/zenodo.23884883](https://doi.org/10.5281/zenodo.23884883). URL: <https://doi.org/10.5281/zenodo.23884883>.

*Commentary.*

C_r(n)=n/D_r(n), with natural division.

**Theorem 1.3 (Roots of zero modulo n).**

Lean statement: `D5/S3/ArithSums/BrowneA164660RootCount.dvd_pow_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BrowneA164660RootCount.dvd_pow_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products*. DOI: [10.5281/zenodo.23884883](https://doi.org/10.5281/zenodo.23884883). URL: <https://doi.org/10.5281/zenodo.23884883>.

*Commentary.*

For every integer k, n ∣ k^r if and only if D_r(n) ∣ k. For k=0 both hold. Otherwise compare p-adic valuations: e_p ≤ r·v_p(k) is equivalent to ⌈e_p/r⌉ ≤ v_p(k), and D_r(n) has exponent ⌈e_p/r⌉ at each p.

**Theorem 1.4 (Translated windows).**

Lean statement: `D5/S3/ArithSums/BrowneA164660RootCount.window`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BrowneA164660RootCount.window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products*. DOI: [10.5281/zenodo.23884883](https://doi.org/10.5281/zenodo.23884883). URL: <https://doi.org/10.5281/zenodo.23884883>.

*Commentary.*

For every integer s, over k=s+1,…,s+n the floor differences ⌊k^r/n⌋−⌊(k^r−1)/n⌋ sum to C_r(n), and the product of 1−2 times them is (−1)^(C_r(n)). Each difference is 1 when n ∣ k^r and 0 otherwise, so the sum counts multiples of D_r(n) in (s,s+n]; since D_r(n) ∣ n, that count is ⌊(s+n)/D_r(n)⌋−⌊s/D_r(n)⌋=n/D_r(n), including windows that contain zero or negative integers.

**Theorem 1.5 (When the count is n/rad(n)).**

Lean statement: `D5/S3/ArithSums/BrowneA164660RootCount.threshold`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BrowneA164660RootCount.threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products*. DOI: [10.5281/zenodo.23884883](https://doi.org/10.5281/zenodo.23884883). URL: <https://doi.org/10.5281/zenodo.23884883>.

*Commentary.*

For n>1, C_r(n)=n/rad(n) exactly when r ≥ e_p for every prime p ∣ n; for n=1 both sides are 1. Indeed C_r(n)=n/rad(n) means D_r(n)=rad(n), that is ⌈e_p/r⌉=1 for every p ∣ n, and since e_p ≥ 1 this is e_p ≤ r.

**Theorem 1.6 (Identification with A164660).**

Lean statement: `D5/S3/ArithSums/BrowneA164660RootCount.window_eq_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/BrowneA164660RootCount.window_eq_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anthony Browne; Wolfdieter Lang (2016). *OEIS A164660: Chebyshev row numerators and Browne's floor product*. URL: <https://oeis.org/search?q=id:A164660&fmt=text>.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products*. DOI: [10.5281/zenodo.23884883](https://doi.org/10.5281/zenodo.23884883). URL: <https://doi.org/10.5281/zenodo.23884883>.

*Commentary.*

For r ≥ 2 and every integer s the translated product equals a(n+1). The 2-adic valuation of C_r(n) is e_2−⌈e_2/r⌉, which is positive exactly when e_2 ≥ 2, so C_r(n) is even exactly when 4 ∣ n; the Chebyshev numerator evaluation gives a(n+1)=1 when 4 ∣ n and −1 otherwise.

## References

- Truth anchor: `D5/S3/ArithSums/BrowneA164660RootCount.C`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660RootCount.D`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660RootCount.dvd_pow_iff`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660RootCount.threshold`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660RootCount.window`
- Truth anchor: `D5/S3/ArithSums/BrowneA164660RootCount.window_eq_numerator`
- Dependency: [D5/S3/ArithSums/BrowneA164660ChebyshevFloorProduct](BrowneA164660ChebyshevFloorProduct.md)
