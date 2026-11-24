# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Definition 1.1 (The row-major order).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229585Strip}}.\operatorname{\mathit{cellOrder}}\left(n\right) : \operatorname{\mathit{LinearOrder}}\left((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right))\right)) = \operatorname{\mathit{LinearOrder}}.\operatorname{\mathit{lift}}'\left(\operatorname{\mathit{finProdFinEquiv}}, \operatorname{\mathit{Equiv}}.\operatorname{\mathit{injective}}\left(\operatorname{\mathit{finProdFinEquiv}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.cellOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The order is pulled back from the finite ordinal using the index seven times the row plus the column.

**Definition 1.2 (First occurrences of colours).**

$$\forall n: \mathit{Nat}, (\forall f: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{HardinA229585Strip}}.\operatorname{\mathit{Normal}}\left(f\right)) \iff (\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right)), \operatorname{\mathit{Preorder}}.\operatorname{\mathit{toLT}}\left(\operatorname{\mathit{PartialOrder}}.\operatorname{\mathit{toPreorder}}\left(\operatorname{\mathit{LinearOrder}}.\operatorname{\mathit{toPartialOrder}}\left(\operatorname{\mathit{HardinA229585Strip}}.\operatorname{\mathit{cellOrder}}\left(n\right)\right)\right)\right), 3, f\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.Normal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The comparison of cell positions uses the row-major order.

**Theorem 1.3 (Antidiagonal defect count).**

$$\forall r: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}, (\forall t: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}}, r, t\right) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Only the six-cell tail of the preceding row is used by antidiagonal bonds.

**Theorem 1.4 (Relabelling preserves a class).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, p\right), d\right) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.class_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

A bijection of the palette preserves all colour equalities.

**Theorem 1.5 (Relabelling preserves horizontal defects).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall r: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right), \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right)\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.horizontal_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Relabelling both endpoints preserves the monochromatic status of every horizontal bond.

**Theorem 1.6 (Relabelling preserves antidiagonal charge).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall r: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, p\right), \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right)\right) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.cross_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The same colour permutation acts on the preceding boundary and the next row.

**Definition 1.7 (The literal normalized array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(7\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(7\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 7 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 7 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The finite filter ranges over all arrays. The ordinal 7*i+j orders cells row by row. Each colour has earlier occurrences of all smaller colours, so the first cell is zero whenever the array is nonempty.

**Theorem 1.8 (The complete finite transfer certificate).**

$$(\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \mathit{Row}, ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(72\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \mathit{Row}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(72\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(10\right), (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(10\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(8\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-656100), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1574640, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-1513404), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(750384, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-206469), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(31428, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-2466), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(84, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{ofNat}}\left(11, 2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The first two clauses preserve the exact residual budget. The next three clauses give all class transition and initial counts. The final clauses verify each forward-table step and its polynomial relation. Finite indices in the last clause have value 2+j and satisfy 2+j < 11.

**Theorem 1.9 (The order-eight forward-vector relation).**

$$\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{initial}}, 2 + 8\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(8\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-656100), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1574640, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-1513404), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(750384, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-206469), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(31428, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-2466), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(84, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{initial}}, 2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.polynomial_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The finite transfer certificate gives the vector relation at shift two. The forward iterates use the width-seven transfer and its initial weights.

**Theorem 1.10 (The integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 9\right): \mathit{Int}) = 84 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 8\right): \mathit{Int}) - 2466 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) + 31428 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) - 206469 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) + 750384 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) - 1513404 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) + 1574640 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) - 656100 \cdot (\operatorname{\mathit{HardinA229585Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229585` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229585","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

All natural counts in this equality are cast to integers. Relabelling the three colours gives six labelled arrays for each canonical array once at least two colours occur. The transfer relation then yields this recurrence with the displayed index shifts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.Normal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.cellOrder`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.class_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.cross_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.edge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.horizontal_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.polynomial_relation`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripCertificate](HardinA229585StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](HardinA229585StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbitCertificate](HardinA229585StripOrbitCertificate.md)
