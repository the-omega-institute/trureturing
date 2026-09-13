# The OEIS A018800 Prime-Prefix Suffix-Bound Conjecture

## Abstract

The value a(1) = 11 refutes Murthy's suffix bound for OEIS A018800.

**Definition 1.1 (The A018800 sequence).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{sInf}\left(\{p \in \mathrm{Nat} \mid (\operatorname{Prime}\left(p\right)) \land (\exists m \in \mathrm{Nat},\; (n \cdot 10^{m} \le p) \land (p < \left(n + 1\right) \cdot 10^{m}))\}\right)$$

*Formalization.* `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.a` (`✓ std3`).

*Citation.* Amarnath Murthy; David W. Wilson (2002). *OEIS A018800, Smallest prime that begins with n*. URL: <https://oeis.org/A018800>.

*Commentary.*

The interval condition expresses the decimal-prefix reading of begins with n. The natural infimum is zero when the set is empty.

**Definition 1.2 (Murthy's suffix-bound conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; 1 \le n \Rightarrow \left(1 \le m \Rightarrow \left(k < 10^{m} \Rightarrow \left(\operatorname{a}\left(n\right) = n \cdot 10^{m} + k \Rightarrow k < n\right)\right)\right))$$

*Formalization.* `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.claim` (`✓ std3`).

*Citation.* Amarnath Murthy; David W. Wilson (2002). *OEIS A018800, Smallest prime that begins with n*. URL: <https://oeis.org/A018800>.

*Commentary.*

The positive suffix length makes the appended suffix nonempty. Its value is below 10 to that length, and the conjecture requires it to be strictly smaller than the prefix.

**Theorem 1.3 (The conjecture fails at n = 1).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a018800-least-prime-prefix-suffix-refutation` (refuted) by `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a018800-least-prime-prefix-suffix-refutation","declaration_gid":"D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amarnath Murthy; David W. Wilson (2002). *OEIS A018800, Smallest prime that begins with n*. URL: <https://oeis.org/A018800>.

*Commentary.*

At n = 1, the least prime with decimal prefix 1 is a(1) = 11. Taking a suffix of length one and value one gives 11 = 1 times 10 plus 1, while one is not strictly smaller than one. No general existence statement for a(n) is asserted.

## References

- Truth anchor: `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.a`
- Truth anchor: `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.claim`
- Truth anchor: `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.result`
