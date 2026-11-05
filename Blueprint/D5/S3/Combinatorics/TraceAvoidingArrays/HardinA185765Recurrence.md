# HardinA185765Recurrence

## Abstract

Six-column binary arrays and Hardin's trace-avoidance recurrence.

**Definition 1.1 (Hardin’s empirical recurrence).**

$$(claim) \Leftrightarrow (\forall (n : \mathbb{N}), (13 \le n) \Rightarrow ((\operatorname{a}\left(n\right) : \mathbb{Z}) = (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + 30 \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + 24 \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) - 95 \cdot (\operatorname{a}\left(n - 4\right) : \mathbb{Z}) - 15 \cdot (\operatorname{a}\left(n - 5\right) : \mathbb{Z}) + 64 \cdot (\operatorname{a}\left(n - 6\right) : \mathbb{Z}) - 116 \cdot (\operatorname{a}\left(n - 7\right) : \mathbb{Z}) + 16 \cdot (\operatorname{a}\left(n - 8\right) : \mathbb{Z}) + 16 \cdot (\operatorname{a}\left(n - 9\right) : \mathbb{Z})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.claim` (`✓ std3`).

*Citation.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Empirical: a(n)=a(n-1)+30*a(n-2)+24*a(n-3)-95*a(n-4)-15*a(n-5)+64*a(n-6)-116*a(n-7)+16*a(n-8)+16*a(n-9) for n>12 Sole FORMULA field, OEIS A185765 revision 9, without page numbering. The count a is the preceding finite cardinality. Natural subtraction is truncated; all ten indices are positive when n is at least thirteen. Counts are embedded in the integers before signed operations.

**Definition 1.2 (The vector residual).**

$$\forall (k : \mathbb{N}), \operatorname{residual}\left(k\right) = \operatorname{u}\left(k + 9\right) - \operatorname{u}\left(k + 8\right) - \operatorname{HSMul.hSMul}\left((30 : \mathbb{Z}), \operatorname{u}\left(k + 7\right)\right) - \operatorname{HSMul.hSMul}\left((24 : \mathbb{Z}), \operatorname{u}\left(k + 6\right)\right) + \operatorname{HSMul.hSMul}\left((95 : \mathbb{Z}), \operatorname{u}\left(k + 5\right)\right) + \operatorname{HSMul.hSMul}\left((15 : \mathbb{Z}), \operatorname{u}\left(k + 4\right)\right) - \operatorname{HSMul.hSMul}\left((64 : \mathbb{Z}), \operatorname{u}\left(k + 3\right)\right) + \operatorname{HSMul.hSMul}\left((116 : \mathbb{Z}), \operatorname{u}\left(k + 2\right)\right) - \operatorname{HSMul.hSMul}\left((16 : \mathbb{Z}), \operatorname{u}\left(k + 1\right)\right) - \operatorname{HSMul.hSMul}\left((16 : \mathbb{Z}), \operatorname{u}\left(k\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The residual applies the nine coefficients of the recurrence to consecutive continuation vectors, with scalar multiplication over the integers.

**Definition 1.3 (Three finite equalities).**

$$(Certificate) \Leftrightarrow ((\operatorname{residual}\left(5\right) = 0) \land ((\sum_{r : \operatorname{Fin}\left(64\right)} (\sum_{s : \operatorname{Fin}\left(64\right)} (\operatorname{residual}\left(3\right)\left(r, s\right))) = 0) \land (\sum_{r : \operatorname{Fin}\left(64\right)} (\sum_{s : \operatorname{Fin}\left(64\right)} (\operatorname{residual}\left(4\right)\left(r, s\right))) = 0)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The vector residual at five is zero, and the scalar totals at three and four are zero.

**Theorem 1.4 (The three equalities hold).**

$$(\operatorname{residual}\left(5\right) = 0) \land ((\sum_{r : \operatorname{Fin}\left(64\right)} (\sum_{s : \operatorname{Fin}\left(64\right)} (\operatorname{residual}\left(3\right)\left(r, s\right))) = 0) \land (\sum_{r : \operatorname{Fin}\left(64\right)} (\sum_{s : \operatorname{Fin}\left(64\right)} (\operatorname{residual}\left(4\right)\left(r, s\right))) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

The literal tables satisfy every transfer step through fourteen, the vector residual at five vanishes, and the scalar residual totals at three and four vanish.

**Theorem 1.5 (The recurrence holds for every stated index).**

$$\forall (n : \mathbb{N}), (13 \le n) \Rightarrow ((\operatorname{a}\left(n\right) : \mathbb{Z}) = (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + 30 \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + 24 \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) - 95 \cdot (\operatorname{a}\left(n - 4\right) : \mathbb{Z}) - 15 \cdot (\operatorname{a}\left(n - 5\right) : \mathbb{Z}) + 64 \cdot (\operatorname{a}\left(n - 6\right) : \mathbb{Z}) - 116 \cdot (\operatorname{a}\left(n - 7\right) : \mathbb{Z}) + 16 \cdot (\operatorname{a}\left(n - 8\right) : \mathbb{Z}) + 16 \cdot (\operatorname{a}\left(n - 9\right) : \mathbb{Z}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin185765` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin185765","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2011). *OEIS A185765: six-column binary arrays with unequal neighboring subblock traces*. URL: <https://oeis.org/A185765>.

*Commentary.*

Linearity propagates the vanishing vector residual from five onward. The scalar equalities at three and four cover indices thirteen and fourteen. The counting identity then gives the stated recurrence for every n at least thirteen.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.Certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.residual`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer](HardinA185765Transfer.md)
