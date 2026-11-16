# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Definition 1.1 (The literal normalized array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229583Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

The finite filter ranges over all arrays. The ordinal i*k+j orders cells row by row. Each colour has earlier occurrences of all smaller colours, so the first cell is zero whenever the array is nonempty.

**Theorem 1.2 (Boundary compression preserves antidiagonal defects).**

$$\forall r: \mathit{Row}, (\forall t: \mathit{Row}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}}, r, t\right) = \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

The antidiagonal bond filter depends on the preceding row only through its four boundary colours.

**Theorem 1.3 (The complete finite transfer certificate).**

$$(\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \mathit{Row}, ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(14\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229583StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \mathit{Row}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(14\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(5\right), (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229583StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{W}\left(5\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(4\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-324), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(540, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-261), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(30, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229583StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

The first two clauses preserve the exact residual budget. The next three clauses give all class transition and initial counts. The final clauses verify each forward-table step and its polynomial relation. Finite indices in the last clause have value 1+j and bound 1+j < 6.

**Theorem 1.4 (The integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229583Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) = 30 \cdot (\operatorname{\mathit{HardinA229583Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) - 261 \cdot (\operatorname{\mathit{HardinA229583Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) + 540 \cdot (\operatorname{\mathit{HardinA229583Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) - 324 \cdot (\operatorname{\mathit{HardinA229583Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229583` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229583","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

All natural counts in this equality are cast to integers. Relabelling the three colours gives six labelled arrays for each canonical array once at least two colours occur. The transfer relation then yields this recurrence with the displayed index shifts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.edge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripCertificate](HardinA229583StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses0](HardinA229583StripClasses0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses1](HardinA229583StripClasses1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses2](HardinA229583StripClasses2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses3](HardinA229583StripClasses3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses4](HardinA229583StripClasses4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses5](HardinA229583StripClasses5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripClasses6](HardinA229583StripClasses6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData](HardinA229583StripData.md)
