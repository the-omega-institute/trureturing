# A397436 Conjecture 3: the unrestricted congruence is false

## Abstract

A one-factor positive instance refutes the unrestricted signed product congruence.

**Definition 1.1 (The inclusive signed binomial-product sum).**

$$\forall r \in \mathbb{N},\; \forall m \in \operatorname{IntVector}\left(r\right),\; \forall M \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{U}\left(m, M, n\right) = \sum_{k \in \operatorname{Icc}\left(0, M \cdot n\right)} {\operatorname{Product}\left(i, \operatorname{Fin}\left(r\right), \operatorname{RingChoose}\left(\operatorname{m}\left(i\right) \cdot \operatorname{NatCast}\left(n\right), k\right)\right)}$$

*Formalization.* `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; OEIS Foundation Inc. (2026). *OEIS A397436 revision 44, Conjecture 3 on integer-parameter binomial products*. URL: <https://oeis.org/A397436/internal>.

*Commentary.*

For natural r, m is a function Fin r to the integers. Ring.choose is the generalized binomial on integer upper arguments, including negative values. The sum includes k=0 and k=M*n; the product runs over all r indices. NatCast embeds n into the integers before multiplication by m(i). No zero-for-negative-upper convention is used.

**Definition 1.2 (The full same-r universal assertion).**

$$\forall r \in \mathbb{N},\; 0 < r \Rightarrow \left(\forall m \in \operatorname{IntVector}\left(r\right),\; \forall M \in \mathbb{N},\; 0 < M \Rightarrow \left(\forall p \in \mathbb{N},\; \left(\operatorname{Prime}\left(p\right) \land 5 \le p\right) \Rightarrow \operatorname{Divides}\left(\operatorname{NatCast}\left(p\right)^{3 \cdot r}, \operatorname{U}\left(m, M, p^{r}\right) - \operatorname{U}\left(m, M, p^{\operatorname{NatSub}\left(r, 1\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; OEIS Foundation Inc. (2026). *OEIS A397436 revision 44, Conjecture 3 on integer-parameter binomial products*. URL: <https://oeis.org/A397436/internal>.

*Commentary.*

IntVector(r) means Fin r to the integers; Prime is natural primality. The same positive r controls factor count, both lifting exponents and the exponent 3*r of the modulus. NatSub is natural subtraction; r>0 makes r-1 the source exponent. M is any positive natural and m is unrestricted. This encodes the literal item 3, with no restrictions imported from items 1 or 2.

**Theorem 1.3 (The universal assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397436-general-supercongruence` (refuted) by `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397436-general-supercongruence","declaration_gid":"D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; OEIS Foundation Inc. (2026). *OEIS A397436 revision 44, Conjecture 3 on integer-parameter binomial products*. URL: <https://oeis.org/A397436/internal>.

*Commentary.*

Set r=1, m(0)=1, M=1 and p=5. All domain conditions hold. Ring.choose_natCast changes the single factor to Nat.choose. The inclusive rows are [1,5,10,10,5,1] and [1,1], giving U(5)=32 and U(1)=2. Their difference is 30; the required modulus is 125 and does not divide 30. Instantiating the full signed universal claim therefore gives a contradiction. The proof is an application of existing binomial semantics and finite arithmetic; its admission is the named external problem resolution. This addresses only unrestricted Conjecture 3. It makes no conclusion about Conjectures 1 or 2, the special negative-parameter two-factor case, an unprinted restriction or the author's intended relationship between factor and lift indices.

## References

- Truth anchor: `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.U`
- Truth anchor: `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.claim`
- Truth anchor: `D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.result`
