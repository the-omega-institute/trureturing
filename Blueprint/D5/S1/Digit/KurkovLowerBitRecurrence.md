# Kurkov's Lower-Bit Recurrence

## Abstract

Binary prefix products give the complete lower-bit recurrence for A284005.

The sequence a is the imported A284005 function from KurkovWeightProductBinomial, and wt is the imported binary digit sum from DyadicRowPolynomialRecurrence. All variables and operations below are natural: div is floor division, mod is remainder, and log is Nat.log. For n>1 put L=log(2,n) and m=n-2^L. The sum is over every k in Finset.range L. Its bit is div(n,2^k) mod 2. At an existing one bit its summand is a(m), so repeated existing-one contributions are included. The statement is the lower-bit formula attributed to Mikhail Kurkov in A284005, November 10, 2019.

**Theorem 1.1 (The full lower-bit identity and initial data).**

$$(\operatorname{a}\left(0\right) = 1) \land (\operatorname{a}\left(1\right) = 2) \land (\forall n \in \mathbb{N}, 1 < n \Rightarrow \operatorname{a}\left(n\right) = (1 + \operatorname{wt}\left(n\right)) \cdot \operatorname{a}\left(\operatorname{div}\left(n, 2\right)\right)) \land (\forall n \in \mathbb{N}, 1 < n \Rightarrow \operatorname{a}\left(n\right) = 2 \cdot \operatorname{a}\left(n - 2^{\operatorname{log}\left(2, n\right)}\right) + \sum_{k = 0}^{\operatorname{log}\left(2, n\right) - 1} \operatorname{a}\left(n - 2^{\operatorname{log}\left(2, n\right)} + 2^{k} \cdot (1 - \operatorname{mod}\left(\operatorname{div}\left(n, 2^{k}\right), 2\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/KurkovLowerBitRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a284005-kurkov-lower-bit-recurrence` (proved) by `D5/S1/Digit/KurkovLowerBitRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a284005-kurkov-lower-bit-recurrence","declaration_gid":"D5/S1/Digit/KurkovLowerBitRecurrence.result","resolution_kind":"proved"} -->

*Citation.* Mikhail Kurkov; Antti Karttunen; OEIS contributors (2019). *OEIS A284005: Kurkov's full lower-bit recurrence*. URL: <https://oeis.org/A284005>.

*Commentary.*

For an arbitrary depth L and m<2^L define P(L,c,m) as the product, for i<L, of c+wt(div(m,2^i)). The native recurrence gives a(m)=P(L,1,m) and a(2^L+m)=2*P(L,2,m), including m=0 and leading zero padding. Setting a zero bit at position k increases each prefix weight through position k by one and preserves all higher prefix weights. Induction on binary depth gives (c+1)*P(L,c+1,m)=(c+1+wt(m))*P(L,c,m)+Z(L,c,m), where Z is the sum of P(L,c,m+2^k) over the zero positions. The remaining positions contribute wt(m)*P(L,c,m). Taking c=1 and the exact logarithmic leading-power bounds gives the displayed whole sum. The original domain includes n=2 and every power of two; no identity at n=0 or n=1 is asserted. The initial values and defining recurrence are included separately. The source supplies the question; the native proof is a repository result. Importing the sequence from KurkovWeightProductBinomial does not use its two-parameter binomial theorem. No literature proof, global openness or priority is asserted.

## References

- Truth anchor: `D5/S1/Digit/KurkovLowerBitRecurrence.result`
- Dependency: [D5/S1/Digit/KurkovWeightProductBinomial](KurkovWeightProductBinomial.md)
