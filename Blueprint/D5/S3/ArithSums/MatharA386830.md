# Mathar's A386830 recurrence and ordinary D-finiteness

## Abstract

The literal inclusive integer sum A386830 satisfies Mathar's recurrence at every natural n>=2 and has a nonzero homogeneous ordinary formal differential operator.

The sequence is defined at every natural index, including zero. Both finite-sum endpoints are included. Binomial coefficients and exponents are natural, while the summands are integers. In the recurrence n is cast to the integers before coefficient subtraction; backshift indices remain natural under n>=2. The source has OFFSET 0,2 and states no onset: n>=2 is the adopted nonnegative-backshift interpretation, not an author-stated bound or the meaning of the second OFFSET component.

**Definition 1.1 (Literal inclusive NAME sum).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right)=\sum_{k=0}^{n} 3^{k} \cdot 2^{n - k} \cdot \operatorname{choose}\left(3 \cdot n + 1, k\right) \cdot \operatorname{choose}\left(3 \cdot n - k, n - k\right)$$

*Formalization.* `D5/S3/ArithSums/MatharA386830.a` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama (2025). *OEIS A386830: inclusive binomial sum, recurrence and D-finiteness conjecture*. URL: <https://oeis.org/A386830>.

*Commentary.*

This is Manyama's original NAME in OEIS A386830, revision 10. No other FORMULA equivalence is assumed.

**Definition 1.2 (Entire ordinary rational formal series).**

$$series=\sum_{n=0}^{\infty} \operatorname{a}\left(n\right) \cdot z^{n}$$

*Formalization.* `D5/S3/ArithSums/MatharA386830.series` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama (2025). *OEIS A386830: inclusive binomial sum, recurrence and D-finiteness conjecture*. URL: <https://oeis.org/A386830>.

*Commentary.*

The coefficient at every natural index is the literal integer a(n), cast into Q. This is the entire ordinary Q[[z]] series, without an analytic convergence premise.

**Theorem 1.3 (Full recurrence and nonzero homogeneous operator).**

$$(\forall n:\mathbb{N}, 2 \le n \implies 8 \cdot n \cdot \left(2 \cdot n - 3\right) \cdot \operatorname{a}\left(n\right) + 6 \cdot \left(-108 \cdot n^{2} + 207 \cdot n - 80\right) \cdot \operatorname{a}\left(n - 1\right) + 405 \cdot \left(3 \cdot n - 2\right) \cdot \left(3 \cdot n - 4\right) \cdot \operatorname{a}\left(n - 2\right)=0) \land (\exists r:\mathbb{N}, \exists p:\mathbb{N} \to \mathbb{Q}[z], (\exists j:\mathbb{N}, 0 \le j \le r \land \operatorname{p}\left(j\right) \neq 0)\land \sum_{j=0}^{r} \operatorname{p}\left(j\right) \cdot series^{(j)}=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/MatharA386830.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a386830-recurrence-dfinite` (proved) by `D5/S3/ArithSums/MatharA386830.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a386830-recurrence-dfinite","declaration_gid":"D5/S3/ArithSums/MatharA386830.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama (2025). *OEIS A386830: inclusive binomial sum, recurrence and D-finiteness conjecture*. URL: <https://oeis.org/A386830>.

*Commentary.*

The first conjunct covers every natural n>=2. The second quantifies over polynomial coefficients indexed by the naturals and requires a nonzero member between 0 and r. The expression series superscript (j) denotes j-fold formal differentiation, with the zero-fold derivative equal to series, and each polynomial is embedded in Q[[z]]. An explicit order-three witness is p0=3240, p1=-588+25110z, p2=8-1998z+21870z squared, p3=16z-648z squared+3645z cubed. The constant p0 is nonzero. This is one conjunction from one source event, not two resolution credits; minimal order is not claimed.

Expanding 5=3+2 and interchanging finite triangular sums reduces the original NAME to the alternating sum of 5 to the j times (-2) to the (n-j) times choose(3n+1,j). Nat.choose_mul and Int.alternating_sum_range_choose_eq_choose establish the equality for all n, including zero.

Three Pascal expansions and the finite geometric-sum identity give 4a(n)-27a(n-1)=9b(n) for all n>=1, where b(n)=5 to the n times choose(3n-2,n). Cross-multiplied adjacent-binomial identities give 2n(2n-3)b(n)=15(3n-2)(3n-4)b(n-1) for all n>=2. Eliminating b yields exactly the displayed integer recurrence, including its n=2 boundary.

Coefficient comparison proves the displayed homogeneous differential equation directly: the coefficient at index n is n+1 times the recurrence at n+2. Thus every coefficient vanishes, rather than a finite truncation. No EGF or negative-index extension is substituted.

Quoted source material is attributed to The Online Encyclopedia of Integer Sequences, https://oeis.org/A386830, under CC-BY-SA-4.0. Sequence: Seiichi Manyama, Aug 05 2025; conjecture: R. J. Mathar, Aug 19 2025. Worldwide solvedness and priority remain ASSUMED-UNVERIFIED beyond the bounded qualification in the library note. The four-slot audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/30408; typed family evidence does not imply declared_validated.

## References

- Truth anchor: `D5/S3/ArithSums/MatharA386830.a`
- Truth anchor: `D5/S3/ArithSums/MatharA386830.result`
- Truth anchor: `D5/S3/ArithSums/MatharA386830.series`
