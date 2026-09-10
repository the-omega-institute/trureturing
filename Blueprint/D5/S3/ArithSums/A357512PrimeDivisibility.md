# A357512: fourth-power divisibility at composite indices

## Abstract

The fifth-weighted Apery sum at n-1 is divisible by n^4 for every odd n not divisible by three, including composite indices.

With offset zero, a(n) sums k^5 choose(n,k)^2 choose(n+k,k)^2 over 0<=k<=n. The theorem proves the conjecture in the OEIS formula section for all n congruent to 1 or 5 modulo 6.

**Theorem 1.1 (Divisibility for every admissible natural index).**

$$\forall n \in \mathbb{N},\; \left(Odd\left(n\right) \land \neg{3 \mid n}\right) \Rightarrow n^{4} \mid a\left(n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A357512PrimeDivisibility.fourth_dvd_of_odd_not_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2022). *A357512 — fifth-weighted Apery sums and fourth-power divisibility*. URL: <https://oeis.org/search?q=id:A357512&fmt=json>.

*Commentary.*

Two binomial identities first extract n^2 exactly. Put c(k)=choose(n-1,k)choose(n+k,k). Its recurrence gives (k+1)^2(c(k+1)+c(k))=n^2 c(k), together with an integer witness for n dividing (k+1)(c(k+1)+c(k)).

Multiply these identities by c(k+1)-c(k). Modulo n^2, twelve times each remaining summand is the difference of consecutive boundary terms. Summing cancels the interior boundaries; the two endpoints vanish modulo n^2.

Since n is odd and three does not divide n, twelve is coprime to n^2 and can be cancelled. The exact initial factor supplies the other n^2. No summation index is inverted, so the proof applies to composite n.

## References

- Truth anchor: `D5/S3/ArithSums/A357512PrimeDivisibility.fourth_dvd_of_odd_not_three`
