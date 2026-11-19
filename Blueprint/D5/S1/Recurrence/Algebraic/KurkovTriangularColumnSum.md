# Kurkov's Triangular-Block Column Sum

## Abstract

Every lawful A396981 array satisfies Kurkov's positive-column factorial sum.

**Definition 1.1 (The positive-index block sequence).**

$$(\forall q: \mathbb{N}, (\operatorname{f}\left(q\right) = \min \{s \in \mathbb{N} \mid 2 \cdot q \leq s \cdot \left(s + 1\right)\})) \land (\forall q: \mathbb{N}, ((0 < q) \implies (\forall s: \mathbb{N}, ((\operatorname{f}\left(q\right) = s) \iff ((1 \leq s) \land ((\left\lfloor\frac{s \cdot \left(s - 1\right)}{2}\right\rfloor < q) \land (q \leq \left\lfloor\frac{s \cdot \left(s + 1\right)}{2}\right\rfloor)))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.f` (`✓ std3`).

*Citation.* Mikhail Kurkov; OEIS Foundation (2026). *OEIS A396981, Conjecture 1: positive-column factorial sum*. URL: <https://oeis.org/A396981>.

*Commentary.*

For q>0, f(q) is the unique integer s>=1 satisfying floor(s(s-1)/2)<q<=floor(s(s+1)/2), namely OEIS A002024. These are natural-number integer quotients (floor division); the rational factorial quotients in the result remain ordinary Q-division. The implementation takes the least s with 2q<=s(s+1); the private characterization proves equivalence with the source inequalities. Its zero value only totalizes the Lean function and supplies no extra source assertion.

**Definition 1.2 (The literal natural-valued array equations).**

$$\forall A: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, (\operatorname{IsArray}\left(A\right) \iff ((\forall q: \mathbb{N}, (A\left(0, q\right) = 1)) \land ((\forall n: \mathbb{N}, ((1 \leq n) \implies (A\left(n, 0\right) = 0))) \land (\forall n: \mathbb{N}, (\forall q: \mathbb{N}, ((1 \leq n) \implies ((1 \leq q) \implies (A\left(n, q\right) = A\left(n, q - \operatorname{f}\left(q\right)\right) + \left(n + \operatorname{f}\left(q\right) - 1\right) \cdot A\left(n - 1, q\right)))))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.IsArray` (`✓ std3`).

*Citation.* Mikhail Kurkov; OEIS Foundation (2026). *OEIS A396981, Conjecture 1: positive-column factorial sum*. URL: <https://oeis.org/A396981>.

*Commentary.*

A has type N -> N -> N. Its zeroth row is one at every column, its zeroth column is zero at every positive row, and at positive n,q it satisfies A(n,q)=A(n,q-f(q))+(n+f(q)-1)A(n-1,q). Natural subtraction agrees with ordinary subtraction on these indices. These are the only array hypotheses.

**Theorem 1.3 (Existence and the complete positive-column identity).**

$$(\exists A: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, (\operatorname{IsArray}\left(A\right))) \land (\forall A: \mathbb{N} \to \mathbb{N} \to \mathbb{N}, ((\operatorname{IsArray}\left(A\right)) \implies (\forall n: \mathbb{N}, (\forall k: \mathbb{N}, ((1 \leq k) \implies ((A\left(n, k + \operatorname{f}\left(k\right) + 1\right): \mathbb{Q}) = \sum_{j = 0}^{n} (\frac{(A\left(j, k\right): \mathbb{Q}) \cdot ((n + \operatorname{f}\left(k\right))!: \mathbb{Q})}{((\operatorname{f}\left(k\right) + j)!: \mathbb{Q})})))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396981-kurkov-conjecture1-positive-column-factorial-sum` (proved) by `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396981-kurkov-conjecture1-positive-column-factorial-sum","declaration_gid":"D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov; OEIS Foundation (2026). *OEIS A396981, Conjecture 1: positive-column factorial sum*. URL: <https://oeis.org/A396981>.

*Commentary.*

There exists A satisfying IsArray, and for every such A, all natural n and all k>=1, (A(n,k+f(k)+1):Q) equals the sum over j=0,...,n of (A(j,k):Q)*((n+f(k))!:Q)/((f(k)+j)!:Q). Factorials are natural factorials cast to Q before ordinary division; every denominator is nonzero. The existence witness is constructed by well-founded recursion on (n,q). The block inequalities prove f(k+f(k)+1)=f(k)+1, so the original array recurrence at the shifted column is a first-order row recurrence. Induction on n and the factorial successor identity give the inclusive sum, including n=0. The prefatory Stirling identity, Conjectures 2–4 and k=0 are outside this theorem. Source: Mikhail Kurkov and OEIS Foundation, CC-BY-SA 4.0.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.IsArray`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.f`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.result`
