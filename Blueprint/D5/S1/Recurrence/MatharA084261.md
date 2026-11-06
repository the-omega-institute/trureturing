# Mathar's recurrence for OEIS A084261

## Abstract

The literal even-index binomial-factorial sum satisfies Mathar's recurrence at every natural index at least three.

**Definition 1.1 (The literal inclusive sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) : \mathbb{N} = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(n, 2\right) + 1\right)} \operatorname{Nat}.\operatorname{choose}\left(n, 2 \cdot k\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(k\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA084261.a` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry (2012). *OEIS A084261, A binomial transform of factorial numbers*. URL: <https://oeis.org/A084261>.

*Commentary.*

OEIS A084261 defines a(n) as Sum_{k=0..floor(n/2)} C(n,2*k)*k!. The index n, binomial coefficient, factorial, and sum are natural numbers. Nat.div(n,2) is floor(n/2). Finset.range(n/2+1) contains every natural k from zero through floor(n/2), including both endpoints.

**Definition 1.2 (The complete conjectured recurrence).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (2 \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) - 4 \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + (2 - (n : \mathbb{Z})) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + ((n : \mathbb{Z}) - 2) \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) = 0))$$

*Formalization.* `D5/S1/Recurrence/MatharA084261.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry (2012). *OEIS A084261, A binomial transform of factorial numbers*. URL: <https://oeis.org/A084261>.

*Commentary.*

The source FORMULA field attributes 2*a(n)-4*a(n-1)+(-n+2)*a(n-2)+(n-2)*a(n-3)=0 to R. J. Mathar. The source supplies no recurrence onset: n>=3 is the disclosed interpretation with all indices nonnegative. Indices use natural subtraction; each sequence value and n is cast to the integers before signed coefficient products and sums are evaluated. No additional hypothesis is used.

**Theorem 1.3 (The full recurrence holds).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (2 \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) - 4 \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + (2 - (n : \mathbb{Z})) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + ((n : \mathbb{Z}) - 2) \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA084261.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry (2012). *OEIS A084261, A binomial transform of factorial numbers*. URL: <https://oeis.org/A084261>.

*Commentary.*

Write b(k)=(k/2)! for even k and zero for odd k, and T(c,n)=Sum_{k=0..n} C(n,k)c(k), in the integers. Pascal's identity supplies the shifted-transform relation. Parity and factorial succession give 2*b(k+3)+2*b(k+2)-3*b(k+1)-2*b(k)=k*b(k+1)+k*b(k). The weighted binomial identity, with its vanishing boundary terms and justified subtraction cast, then eliminates the shifted transforms. A nonzero-summand bijection k -> k/2 identifies T(b,n) with the literal finite sum, including odd-term vanishing and both endpoints. Substituting n=m+3 covers every n>=3. The proof is bind-only after inlining normalization and upstream identities; the intended admission basis is open-problem-resolution under issue #27208, with utility none. No escape witness or worldwide novelty is claimed. The domain is inhabited (n=3); a(0)=1 and a(2)=2 distinguish actual observations, and the constant-one sequence fails the same law at n=3. The typed Reg mirror attempts source reconstruction, variation and sensitivity. Compilation alone does not establish declared_validated. Canonical freeze, independent form and mirror reviews, current binding evaluation, a Problems dossier, the resolution claim, and required CI remain publication obligations. This document carries no frozen-resolution or publication claim.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA084261.a`
- Truth anchor: `D5/S1/Recurrence/MatharA084261.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA084261.result`
