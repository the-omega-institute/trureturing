# Mathar's recurrence for OEIS A165433

## Abstract

The literal rational factorial sum defining OEIS A165433 satisfies Mathar's recurrence at every natural index at least three.

**Definition 1.1 (The inclusive rational sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) : \mathbb{Q} = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(n, 2\right) + 1\right)} \frac{(\operatorname{Nat}.\operatorname{choose}\left(n - k, k\right) : \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot k\right) : \mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathbb{Q}) \cdot (2 : \mathbb{Q})^{k}}$$

*Formalization.* `D5/S1/Recurrence/MatharA165433.a` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry (2011). *OEIS A165433*. URL: <https://oeis.org/A165433>.

*Commentary.*

The OEIS FORMULA field gives a(n) = Sum_{k=0..floor(n/2)} C(n-k,k)*(2k)!/(k!*2^k). Both n and k are natural numbers. Nat.div(n,2) is floor(n/2), and Finset.range(n/2+1) includes every k from zero through floor(n/2). The binomial coefficient and factorials are computed in the naturals and cast to the rationals before division. The power of two, products, quotient, and sum are rational. Every index subtraction is natural subtraction.

**Definition 1.2 (The complete recurrence).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (2 \cdot \operatorname{a}\left(n\right) - 3 \cdot \operatorname{a}\left(n - 1\right) + (3 - 2 \cdot (n : \mathbb{Q})) \cdot \operatorname{a}\left(n - 2\right) + (2 \cdot (n : \mathbb{Q}) - 3) \cdot \operatorname{a}\left(n - 3\right) = 0))$$

*Formalization.* `D5/S1/Recurrence/MatharA165433.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry (2011). *OEIS A165433*. URL: <https://oeis.org/A165433>.

*Commentary.*

The source attributes the conjecture 2*a(n)-3*a(n-1)+(3-2*n)*a(n-2)+(2*n-3)*a(n-3)=0 to R. J. Mathar. The source specifies no onset; n>=3 is the interpretation using only nonnegative predecessor indices. The quantifier includes every such natural n without an upper bound. Coefficients use the rational cast of n, and recurrence arithmetic is rational. No analytic premise, eventual qualification, or recurrence-defined replacement sequence is assumed.

**Theorem 1.3 (The literal sum satisfies the recurrence).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (2 \cdot \operatorname{a}\left(n\right) - 3 \cdot \operatorname{a}\left(n - 1\right) + (3 - 2 \cdot (n : \mathbb{Q})) \cdot \operatorname{a}\left(n - 2\right) + (2 \cdot (n : \mathbb{Q}) - 3) \cdot \operatorname{a}\left(n - 3\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA165433.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2011-a165433-recurrence` (proved) by `D5/S1/Recurrence/MatharA165433.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2011-a165433-recurrence","declaration_gid":"D5/S1/Recurrence/MatharA165433.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry (2011). *OEIS A165433*. URL: <https://oeis.org/A165433>.

*Commentary.*

Put t(n,k)=C(n-k,k), b(k)=(2k)!/(k!*2^k), T(c,n)=Sum_{k=0..n} t(n,k)c(k), and W(c,n)=T(k -> k*c(k),n), all evaluated in the rationals. The binomial coefficient is zero when n<2*k. Pascal's identity gives T(c,n+2)=T(c,n+1)+T(k -> c(k+1),n). The binomial multiplicative identity gives (n+1)*(T(c,n+1)-T(c,n))=2*W(c,n+1)-W(c,n). Expanding the three factorial successors and cancelling the nonzero denominator gives b(k+1)=(2*k+1)*b(k), hence T(k -> b(k+1),n)=2*W(b,n)+T(b,n). Apply the Pascal relation at n and n+1 and eliminate the shifted transforms and weighted sums using these identities. This yields the stated recurrence at index n+3. All terms with k>floor(n/2) vanish, so T(b,n) equals the entire defining inclusive sum a(n). Writing any index at least three as n+3 completes the result. No assertion of integrality or of a double-factorial replacement is needed.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA165433.a`
- Truth anchor: `D5/S1/Recurrence/MatharA165433.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA165433.result`
