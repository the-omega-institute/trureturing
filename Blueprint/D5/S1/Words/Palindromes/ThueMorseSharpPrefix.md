# Sharp Factor Two for Thue-Morse Prefixes

## Abstract

The sharp factor-two comparison of the actual ordinary and mixed minimum costs on every zero-start Thue-Morse prefix.

**Theorem 1.1 (An ordinary upper bound by signed weight).**

$$\forall n \in \mathbb{N},\; PL\left(factor\left(n, 0\right)\right) \le 2 \cdot signedWeight\left(int\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseSharpPrefix.prefix_signed_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Write P(n)=PL(factor(n,0)) and W(n)=signedWeight(int(n)). The existing substitution tau maps each letter b to [b,not b,not b,b], preserves palindromes, and gives P(4m)<=P(m). The one-letter Lipschitz inequality bounds both insertion and deletion. Signed-weight arithmetic gives W(4m)=W(m), W(4m+1)=W(m)+1, W(4m+2)=1+min(W(m),W(m+1)), and W(4m+3)=W(m+1)+1. Strong induction handles residues zero and one from 4m, residue three from 4(m+1), and residue two from both neighboring multiples of four. In the latter case the two available upper bounds are 2W(m)+2 and 2W(m+1)+2. The empty prefix has both P and W zero. This all-prefix estimate is used in sharp_factor_two_prefix, in both the universal bound and the native attainer proof.

**Theorem 1.2 (The complete sharp comparison for actual minima).**

$$\left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow PL\left(factor\left(n, 0\right)\right) \le 2 \cdot combinedLength\left(factor\left(n, 0\right)\right)\right) \land \left(\exists n \in \mathbb{N},\; 1 \le n \land \left(PL\left(factor\left(n, 0\right)\right) = 2 \cdot combinedLength\left(factor\left(n, 0\right)\right) \land 0 < PL\left(factor\left(n, 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/ThueMorseSharpPrefix.sharp_factor_two_prefix` (`✓ std3`). ∎

*Resolves.* `Problems/ambroz-kadlec-masakova-pelantova-2019-thue-morse-sharp-factor-two-prefix` (proved) by `D5/S1/Words/Palindromes/ThueMorseSharpPrefix.sharp_factor_two_prefix`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ambroz-kadlec-masakova-pelantova-2019-thue-morse-sharp-factor-two-prefix","declaration_gid":"D5/S1/Words/Palindromes/ThueMorseSharpPrefix.sharp_factor_two_prefix","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Section 6 and Table 1 of Ambroz, Kadlec, Masakova and Pelantova motivate the sharp factor-two comparison. The word is the literal zero-start prefix factor(n,0), with false=a and true=b. P is the minimum number of consecutive nonempty palindrome pieces. C=combinedLength minimizes consecutive nonempty pieces, each a palindrome or an exchange-reversal antipalindrome, on the same word. The existing signed-cut theorem gives W(n)<=C(n), so the signed-weight upper bound proves P(n)<=2C(n) for every positive n. For sharpness take n=2: its word is [false,true], a single antipalindrome but not a palindrome. The signed lower bound and this one-piece factorization give C(2)=1; the ordinary upper bound and impossibility of zero or one palindrome pieces give P(2)=2. Thus the equality is positive. All native minimum evidence at n=2 lives inside this theorem's existential proof branch. No unbounded sharpness family or assertion about shifted factors is needed. The separate Table 2 unbounded equal-cost assertion has different quantifiers.

## References

- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSharpPrefix.prefix_signed_upper`
- Truth anchor: `D5/S1/Words/Palindromes/ThueMorseSharpPrefix.sharp_factor_two_prefix`
- Dependency: [D5/S1/Words/Palindromes/ThueMorseAttainment](ThueMorseAttainment.md)
