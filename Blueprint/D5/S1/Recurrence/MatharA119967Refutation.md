# The printed A119967 recurrence fails at every valid index

## Abstract

The literal signed recurrence printed for OEIS A119967 has positive residual at every index at least four.

**Definition 1.1 (The source finite sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(\operatorname{floor}\left(\frac{n}{2}\right) + 1\right)} \operatorname{choose}\left(n, 2 \cdot k\right) \cdot \operatorname{choose}\left(k, \operatorname{floor}\left(\frac{k}{2}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA119967Refutation.a` (`✓ std3`).

*Citation.* Paul Barry; R. J. Mathar; OEIS Foundation and contributors (2011). *OEIS A119967: printed recurrence for a binomial transform*. URL: <https://oeis.org/A119967/internal>.

*Commentary.*

Paul Barry's sequence is a(n)=sum C(n,2k)C(k,floor(k/2)), with k from zero through floor(n/2), inclusive. The indices, binomial coefficients and sum are natural numbers. Nat.div is floor division and Finset.range(m) contains zero through m-1. In particular this uses C(n,2k), rather than C(n-k,k).

**Definition 1.2 (The unchanged signed expression).**

$$\forall n \in \mathbb{N},\; \operatorname{residual}\left(n\right) = ((n : \mathbb{Z}) + 2) \cdot ((n : \mathbb{Z}) - 3) \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) + (2 + 2 \cdot (n : \mathbb{Z}) - (n : \mathbb{Z})^{2}) \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + (3 \cdot (n : \mathbb{Z}) - 5) \cdot ((n : \mathbb{Z}) - 2) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) - ((n : \mathbb{Z}) - 2) \cdot ((n : \mathbb{Z}) - 3) \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) - ((n : \mathbb{Z}) - 2) \cdot ((n : \mathbb{Z}) - 3) \cdot (\operatorname{a}\left(n - 4\right) : \mathbb{Z})$$

*Formalization.* `D5/S1/Recurrence/MatharA119967Refutation.residual` (`✓ std3`).

*Citation.* Paul Barry; R. J. Mathar; OEIS Foundation and contributors (2011). *OEIS A119967: printed recurrence for a binomial transform*. URL: <https://oeis.org/A119967/internal>.

*Commentary.*

The polynomial coefficients are evaluated in the integers. Each natural sequence value is cast to the integers before multiplication. The sequence lags use natural subtraction; for n at least four they are the usual nonnegative indices. All five signs and coefficients are exactly those printed by R. J. Mathar in OEIS A119967.

**Definition 1.3 (The two onset readings).**

$$claim \Leftrightarrow ((\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (\operatorname{residual}\left(n\right) = 0)) \lor (\exists N \in \mathbb{N},\; 4 \le N \land \left(\forall n \in \mathbb{N},\; N \le n \Rightarrow (\operatorname{residual}\left(n\right) = 0)\right)))$$

*Formalization.* `D5/S1/Recurrence/MatharA119967Refutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry; R. J. Mathar; OEIS Foundation and contributors (2011). *OEIS A119967: printed recurrence for a binomial transform*. URL: <https://oeis.org/A119967/internal>.

*Commentary.*

The source prints no recurrence onset. Its offset 0,3 is sequence metadata. The first reading asks for zero residual at every n at least four, the least index with all four lags nonnegative. The second allows any natural cutoff N at least four and asks for zero residual at every n at least N. The disjunction records both interpretations without changing the printed expression.

**Theorem 1.4 (Strict positivity at every valid index).**

$$\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (0 < \operatorname{residual}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA119967Refutation.residual_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry; R. J. Mathar; OEIS Foundation and contributors (2011). *OEIS A119967: printed recurrence for a binomial transform*. URL: <https://oeis.org/A119967/internal>.

*Commentary.*

Every summand is nonnegative and the k=0 summand is one, so a(n) is positive. Monotonicity of C(n,2k) in n and inclusion of the summation ranges show that a is nondecreasing. Write A=(n+2)(n-3) and D=(n-2)(n-3). For n at least four both are nonnegative. The first two terms of the residual equal A(a(n)-a(n-1))+(n-4)a(n-1), hence are nonnegative. The remaining terms equal D(a(n-2)-a(n-3))+D(a(n-2)-a(n-4))+(n-2)(n+1)a(n-2). Their last summand is strictly positive and the other two are nonnegative. Thus the entire residual is positive.

**Theorem 1.5 (Neither onset reading holds).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA119967Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-2011-a119967-recurrence` (refuted) by `D5/S1/Recurrence/MatharA119967Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-2011-a119967-recurrence","declaration_gid":"D5/S1/Recurrence/MatharA119967Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry; R. J. Mathar; OEIS Foundation and contributors (2011). *OEIS A119967: printed recurrence for a binomial transform*. URL: <https://oeis.org/A119967/internal>.

*Commentary.*

At n=4 the source sum gives a(0),...,a(4)=1,1,2,4,9. The five coefficients are 6,-6,14,-2,-2, so the residual is 54. This already contradicts the first reading. For any proposed later cutoff N, positivity at N contradicts zero residual there, excluding the second reading as well. This concerns the printed expression only; no corrected recurrence, generating-function identity or priority assertion is inferred.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA119967Refutation.a`
- Truth anchor: `D5/S1/Recurrence/MatharA119967Refutation.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA119967Refutation.residual`
- Truth anchor: `D5/S1/Recurrence/MatharA119967Refutation.residual_pos`
- Truth anchor: `D5/S1/Recurrence/MatharA119967Refutation.result`
