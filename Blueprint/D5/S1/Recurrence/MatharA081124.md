# Mathar's recurrence for OEIS A081124

## Abstract

The literal binomial transform of floor(k/2)! satisfies Mathar's recurrence at every natural index at least three.

**Definition 1.1 (The literal inclusive sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) : \mathbb{N} = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} \operatorname{Nat}.\operatorname{choose}\left(n, k\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Nat}.\operatorname{div}\left(k, 2\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA081124.a` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry (2012). *OEIS A081124, Binomial transform of floor(n/2)!*. URL: <https://oeis.org/A081124>.

*Commentary.*

OEIS A081124 defines a(n) as Sum_{k=0..n} C(n,k)*floor(k/2)!. The index n, binomial coefficient, factorial, and sum are natural numbers. Nat.div(k,2) is floor(k/2). Finset.range(n+1) contains every natural k from zero through n, including both endpoints.

**Definition 1.2 (The complete conjectured recurrence).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (2 \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) - 4 \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + (2 - (n : \mathbb{Z})) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + ((n : \mathbb{Z}) - 1) \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) = 0))$$

*Formalization.* `D5/S1/Recurrence/MatharA081124.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry (2012). *OEIS A081124, Binomial transform of floor(n/2)!*. URL: <https://oeis.org/A081124>.

*Commentary.*

The source FORMULA field attributes 2*a(n)-4*a(n-1)+(-n+2)*a(n-2)+(n-1)*a(n-3)=0 to R. J. Mathar. The source supplies no recurrence onset: n>=3 is the disclosed interpretation with all indices nonnegative. Indices use natural subtraction; each sequence value and n is cast to the integers before signed coefficient products and sums are evaluated. No additional hypothesis is used.

**Theorem 1.3 (The full recurrence holds).**

$$\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (2 \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) - 4 \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + (2 - (n : \mathbb{Z})) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + ((n : \mathbb{Z}) - 1) \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA081124.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2012-a081124-recurrence` (proved) by `D5/S1/Recurrence/MatharA081124.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2012-a081124-recurrence","declaration_gid":"D5/S1/Recurrence/MatharA081124.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry (2012). *OEIS A081124, Binomial transform of floor(n/2)!*. URL: <https://oeis.org/A081124>.

*Commentary.*

Write b(k)=floor(k/2)! and T(c,n)=Sum_{k=0..n} C(n,k)c(k), evaluated in the integers. The pinned Pascal-sum identity gives T(c,n+1)=T(c,n)+T(k -> c(k+1),n). Parity and the factorial successor identity give 2*b(k+3)+2*b(k+2)-3*b(k+1)-b(k)=k*b(k+1)+k*b(k). The binomial identity C(n,k+1)*(k+1)=C(n,k)*(n-k), with both boundary terms explicitly zero, converts the transformed right side to n*T(k -> b(k+1),n). Eliminating shifted transforms by Pascal's identity yields the recurrence. Cast-through-sum identifies this transform with the entire literal natural sum a(n). No generating function, truncation, or recurrence-defined replacement sequence is assumed.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA081124.a`
- Truth anchor: `D5/S1/Recurrence/MatharA081124.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA081124.result`
