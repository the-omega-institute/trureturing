# Chen and Chen's Eulerian triangle parity positivity

## Abstract

For every integer step at most minus three, two-step propagation makes each positive even row strictly positive.

**Definition 1.1 (The exact boundary and recursion).**

$$\forall m: \mathbb{Z}, (\forall T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right), ((\operatorname{Source}\left(m, T\right)) \iff ((\forall n: \mathbb{N}, ((1 \leq n) \Rightarrow ((T\left(n, 1\right) = 1) \land (T\left(n, n\right) = 1)))) \land (\forall n: \mathbb{N}, (\forall k: \mathbb{N}, ((1 < k) \Rightarrow ((k < n) \Rightarrow (T\left(n, k\right) = (m \cdot ((n: \mathbb{Z}) - (k: \mathbb{Z})) + 1) \cdot T\left(n - 1, k - 1\right) + (m \cdot ((k: \mathbb{Z}) - 1) + 1) \cdot T\left(n - 1, k\right)))))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.Source` (`✓ std3`).

*Citation.* Xin Chen and Yudian Chen (2026). *OEIS A392664, A392665 and A392666: negative-step Eulerian triangles*. URL: <https://oeis.org/A392664>.

*Commentary.*

OEIS A392664, A392665 and A392666 define T(n,1)=T(n,n)=1 for n>=1, and the displayed recursion for 1<k<n, with m=-3,-4,-5 respectively. All values are integers. Row zero and positions outside 1<=k<=n are unconstrained. Subtractions in the two coefficients are integer subtractions; predecessor indices use natural subtraction.

**Definition 1.2 (Existence and universal nonnegativity).**

$$\forall m: \mathbb{Z}, ((\operatorname{ParityPositivity}\left(m\right)) \iff ((\exists T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right), (\operatorname{Source}\left(m, T\right))) \land (\forall T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right), ((\operatorname{Source}\left(m, T\right)) \Rightarrow (\forall n: \mathbb{N}, ((1 \leq n) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (\forall k: \mathbb{N}, ((1 \leq k) \Rightarrow ((k \leq n) \Rightarrow (0 \leq T\left(n, k\right))))))))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.ParityPositivity` (`✓ std3`).

*Citation.* Xin Chen and Yudian Chen (2026). *OEIS A392664, A392665 and A392666: negative-step Eulerian triangles*. URL: <https://oeis.org/A392664>.

*Commentary.*

A solution exists, and every solution has nonnegative entries in each positive even row. Existence is constructed recursively in the row index with arbitrary zero values outside the prescribed triangle. The universal clause applies to every extension, independently of those choices.

**Definition 1.3 (The three conjectures together).**

$$(claim) \iff ((\operatorname{ParityPositivity}\left(-3\right)) \land ((\operatorname{ParityPositivity}\left(-4\right)) \land (\operatorname{ParityPositivity}\left(-5\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.claim` (`✓ std3`).

*Citation.* Xin Chen and Yudian Chen (2026). *OEIS A392664, A392665 and A392666: negative-step Eulerian triangles*. URL: <https://oeis.org/A392664>.

*Commentary.*

The conjunction retains each source parameter separately, including existence and the quantifier over every solution for each parameter.

**Theorem 1.4 (Strict positivity for every integer r at least three).**

$$\forall r: \mathbb{Z}, ((3 \leq r) \Rightarrow (\forall T: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{Z}\right), ((\operatorname{Source}\left(-r, T\right)) \Rightarrow (\forall n: \mathbb{N}, ((1 \leq n) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (\forall k: \mathbb{N}, ((1 \leq k) \Rightarrow ((k \leq n) \Rightarrow (0 < T\left(n, k\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.even_rows_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xin Chen and Yudian Chen (2026). *OEIS A392664, A392665 and A392666: negative-step Eulerian triangles*. URL: <https://oeis.org/A392664>.

*Commentary.*

Let U satisfy the source recursion with m=-r. Reflection follows by row induction because the two recurrence coefficients exchange under k -> n+1-k. Put x(n)=U(n,2). The recursion gives x(2)=1 and x(n+2)=(r-1)^2*x(n)+r*(r-2)*n+2-r^2 for n>=2. In particular x(4)=2*r*(r-3)+3>0. For n>=4 the forcing term is positive: it equals r*(r-2)*(n-4)+3*r*(r-3)+r+2. Thus the second column is positive at every even row, and reflection gives the penultimate column. From a positive even row, both coefficients are negative at every interior position of the next odd row, making its interior negative. At positions 3 through n of row n+2 both predecessors are negative, so both products are positive. The second and penultimate positions use the column argument; the two boundary positions equal one. Induction starts at row two.

**Theorem 1.5 (The complete source conjunction).**

$$(\operatorname{ParityPositivity}\left(-3\right)) \land ((\operatorname{ParityPositivity}\left(-4\right)) \land (\operatorname{ParityPositivity}\left(-5\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-chen-step-m-eulerian-parity-positivity` (proved) by `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-chen-step-m-eulerian-parity-positivity","declaration_gid":"D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xin Chen and Yudian Chen (2026). *OEIS A392664, A392665 and A392666: negative-step Eulerian triangles*. URL: <https://oeis.org/A392664>.

*Commentary.*

Apply the general positivity theorem at r=3,4,5 and weaken strict positivity to nonnegativity. The recursively constructed solution supplies existence for each parameter. No assumption about a finite prefix or about the signs of later rows is used.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.ParityPositivity`
- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.Source`
- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.even_rows_positive`
- Truth anchor: `D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.result`
