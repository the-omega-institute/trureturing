# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Theorem 1.1 (cross_relabel).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Boundary}}, (\forall r: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, p\right), \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right)\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.cross_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The boundary transfer preserves this exact equality under the displayed operations.

**Theorem 1.2 (horizontal_relabel).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall r: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right), \operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right)\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.horizontal_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The boundary transfer preserves this exact equality under the displayed operations.

**Theorem 1.3 (class_relabel).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, p\right), d\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(p, d\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.class_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The boundary transfer preserves this exact equality under the displayed operations.

**Theorem 1.4 (edge).**

$$\forall r: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Row}}, (\forall t: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{antidiagonal}}, r, t\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The boundary transfer preserves this exact equality under the displayed operations.

**Definition 1.5 (The literal normalized array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(6\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 6 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 6 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The finite filter ranges over all arrays. The ordinal i*k+j orders cells row by row. Each colour has earlier occurrences of all smaller colours, so the first cell is zero whenever the array is nonempty.

**Theorem 1.6 (The complete finite transfer certificate).**

$$(\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \mathit{Row}, ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(32\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \mathit{Row}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(32\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(7\right), (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229584StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(7\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-6561), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(14580, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-12150), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4662, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-805), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(50, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The first two clauses preserve the exact residual budget. The next three clauses give all class transition and initial counts. The final clauses verify each forward-table step and its polynomial relation. Finite indices in the last clause have value 1+j.val and bound 1+j.val < 8.

**Theorem 1.7 (The cached forward prefix).**

$$\forall i: \operatorname{\mathit{Fin}}\left(8\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The eight cached vectors are the exact forward iterates of the one-defect transfer. HardinA229692StripInherited uses this prefix for its leading block.

**Theorem 1.8 (The degree-six vector relation).**

$$\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}, 1 + 6\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-6561), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(14580, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-12150), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4662, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-805), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(50, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\left(j\right): \mathit{Int}), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}, 1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.polynomial_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The integer coefficient vector is ordered by increasing forward index. HardinA229692StripInherited transports this relation by powers of the same transfer matrix.

**Theorem 1.9 (The integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) = 50 \cdot (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) - 805 \cdot (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) + 4662 \cdot (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) - 12150 \cdot (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) + 14580 \cdot (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) - 6561 \cdot (\operatorname{\mathit{HardinA229584Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229584` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229584","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

All natural counts in this equality are cast to integers. Relabelling the three colours gives six labelled arrays for each canonical array once at least two colours occur. The transfer relation then yields this recurrence with the displayed index shifts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.class_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.cross_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.edge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.horizontal_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.polynomial_relation`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.powers_table`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate](HardinA229584StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses0](HardinA229584StripClasses0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses1](HardinA229584StripClasses1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses10](HardinA229584StripClasses10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses11](HardinA229584StripClasses11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses12](HardinA229584StripClasses12.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses13](HardinA229584StripClasses13.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses14](HardinA229584StripClasses14.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses15](HardinA229584StripClasses15.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses2](HardinA229584StripClasses2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses3](HardinA229584StripClasses3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses4](HardinA229584StripClasses4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses5](HardinA229584StripClasses5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses6](HardinA229584StripClasses6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses7](HardinA229584StripClasses7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses8](HardinA229584StripClasses8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClasses9](HardinA229584StripClasses9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](HardinA229584StripData.md)
