# Mathar's recurrence for the literal A097967 factorial sum

## Abstract

The literal factorial sum in A097967 satisfies Mathar's recurrence at every natural index at least five.

N denotes the natural numbers and Q the rational numbers. All indices, factorials, descending factorials and index subtractions are natural-number operations. A displayed cast to Q occurs before division or signed scalar arithmetic. Finset.Icc(1,n) includes both endpoints and is empty at n=0; Finset.range(n) contains 0 through n-1.

**Definition 1.1 (The source factorial sum).**

$$\forall n \in \mathbb{N},\; \operatorname{literal}\left(n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} \frac{(\operatorname{Nat}.\operatorname{factorial}\left(n\right) : \mathbb{Q}) \cdot ((\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{Q}) + 1)}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k\right) : \mathbb{Q})}$$

*Formalization.* `D5/S1/Recurrence/MatharA097967.literal` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A097967: sum of permutations and binomial coefficients, recurrence conjecture*. URL: <https://oeis.org/A097967>.

*Commentary.*

The literal FORMULA in the cited OEIS entry is n!(k!+1)/(k!(n-k)!), summed over 1<=k<=n. The NAME describes the same sum as the sum of permutations P(n,k) and binomial coefficients C(n,k). This definition fixes the sequence independently of any recurrence.

**Definition 1.2 (The descending-factorial component).**

$$\forall n \in \mathbb{N},\; \operatorname{b}\left(n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} (\operatorname{Nat}.\operatorname{descFactorial}\left(n, k + 1\right) : \mathbb{Q})$$

*Formalization.* `D5/S1/Recurrence/MatharA097967.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A097967: sum of permutations and binomial coefficients, recurrence conjecture*. URL: <https://oeis.org/A097967>.

*Commentary.*

Nat.descFactorial(n,j) is the natural descending factorial n(n-1)...(n-j+1). Splitting each literal summand gives this component plus the binomial sum. The proof establishes literal(n)=b(n)+2^n-1 and b(n+1)=(n+1)(b(n)+1) internally, using the pinned factorial and binomial identities.

**Definition 1.3 (The complete recurrence claim).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 5 \le n \Rightarrow (\operatorname{literal}\left(n\right) + (0 - (n : \mathbb{Q}) - 6) \cdot \operatorname{literal}\left(n - 1\right) + (6 \cdot (n : \mathbb{Q}) + 7) \cdot \operatorname{literal}\left(n - 2\right) + (-13 \cdot (n : \mathbb{Q}) + 14) \cdot \operatorname{literal}\left(n - 3\right) + 4 \cdot (3 \cdot (n : \mathbb{Q}) - 8) \cdot \operatorname{literal}\left(n - 4\right) + 4 \cdot (0 - (n : \mathbb{Q}) + 4) \cdot \operatorname{literal}\left(n - 5\right) = 0))$$

*Formalization.* `D5/S1/Recurrence/MatharA097967.claim` (`✓ std3`).

*Citation.* R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A097967: sum of permutations and binomial coefficients, recurrence conjecture*. URL: <https://oeis.org/A097967>.

*Commentary.*

The cited FORMULA field attributes the six-term recurrence to Mathar. It supplies no onset. The condition n>=5 is the registered interpretation with nonnegative indices, not an author quotation. There is no upper bound, integrality assumption, negative-index extension, or eventual-only restriction.

**Theorem 1.4 (The literal sum satisfies the recurrence).**

$$\forall n \in \mathbb{N},\; 5 \le n \Rightarrow (\operatorname{literal}\left(n\right) + (0 - (n : \mathbb{Q}) - 6) \cdot \operatorname{literal}\left(n - 1\right) + (6 \cdot (n : \mathbb{Q}) + 7) \cdot \operatorname{literal}\left(n - 2\right) + (-13 \cdot (n : \mathbb{Q}) + 14) \cdot \operatorname{literal}\left(n - 3\right) + 4 \cdot (3 \cdot (n : \mathbb{Q}) - 8) \cdot \operatorname{literal}\left(n - 4\right) + 4 \cdot (0 - (n : \mathbb{Q}) + 4) \cdot \operatorname{literal}\left(n - 5\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA097967.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2013-a097967-literal-recurrence` (proved) by `D5/S1/Recurrence/MatharA097967.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2013-a097967-literal-recurrence","declaration_gid":"D5/S1/Recurrence/MatharA097967.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; OEIS Foundation Inc. (2013). *OEIS A097967: sum of permutations and binomial coefficients, recurrence conjecture*. URL: <https://oeis.org/A097967>.

*Commentary.*

The proof splits the literal sum into b(n)+2^n-1 by the binomial row sum. Five substitutions of b(n+1)=(n+1)(b(n)+1), followed by rational polynomial normalization, give the recurrence at n=m+5. Every n>=5 has this form. The source's printed identity A007526(n)-A000225(n)-1 is not used or certified: at n=1 it gives -1, whereas the literal sum is 2. No other named conjecture or asymptotic formula is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA097967.b`
- Truth anchor: `D5/S1/Recurrence/MatharA097967.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA097967.literal`
- Truth anchor: `D5/S1/Recurrence/MatharA097967.result`
