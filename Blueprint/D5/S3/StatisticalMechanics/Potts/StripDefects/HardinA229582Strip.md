# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Definition 1.1 (Rows).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

A row lists its colours in column order.

**Definition 1.2 (Outgoing boundary).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Boundary}} = (\operatorname{\mathit{Fin}}\left(3\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The tail of a row meets the following row along antidiagonal bonds.

**Definition 1.3 (Horizontal bonds).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(3\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.4 (Antidiagonal bonds).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{antidiagonal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(3\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.antidiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.5 (Retaining the outgoing tail).**

$$\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{boundary}}\left(r\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(r\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

Column zero does not meet the next row.

**Definition 1.6 (Defects between rows).**

$$\forall p: \mathit{Boundary}, (\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cross}}\left(p, r\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(0, p\right), r\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.cross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The inserted zero is outside every antidiagonal bond.

**Definition 1.7 (Admissible residual budgets).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 1) \land (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(2\right) \mapsto (p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le 1 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget.

**Definition 1.8 (Colour permutation classes).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land (p\left(1\right) \neq p\left(2\right))))) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land (p\left(1\right) \neq p\left(2\right))))) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land (p\left(1\right) \neq p\left(2\right))))) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land (p\left(1\right) \neq p\left(2\right))))) \operatorname{\mathit{then}} 3 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land (p\left(1\right) = p\left(2\right))))) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} 5)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

Only equality relations between boundary colours affect continuation counts. The classes also record the remaining defect budget.

**Definition 1.9 (Class transfer matrix).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{T} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(7, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(7, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty.

**Definition 1.10 (Initial labelled row counts).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty.

**Definition 1.11 (Terminal acceptance weights).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty.

**Definition 1.12 (Forward transfer table).**

$$\operatorname{\mathit{HardinA229582Strip}}.\operatorname{W} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(108, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(108, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(72, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(258, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(108, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(258, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(972, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(972, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(648, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4050, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(972, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4050, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(8748, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(8748, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5832, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(52002, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(8748, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(52002, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The finite vector notation is the nested Matrix.vecCons representation, ending in Matrix.vecEmpty.

**Definition 1.13 (The literal normalized array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The finite filter ranges over all arrays. The ordinal i*k+j orders cells row by row. Each colour has earlier occurrences of all smaller colours, so the first cell is zero whenever the array is nonempty.

**Theorem 1.14 (The complete finite transfer certificate).**

$$(\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \mathit{Row}, ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(6\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229582Strip}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \mathit{Row}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(6\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(3\right), (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229582Strip}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{W}\left(3\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(2\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-81), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(18, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\left(j\right), \operatorname{\mathit{HardinA229582Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

The first two clauses preserve the exact residual budget. The next three clauses give all class transition and initial counts. The final clauses verify each forward-table step and its polynomial relation. Finite indices in the last clause have value 1+j and bound 1+j < 4.

**Theorem 1.15 (The integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229582Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) = 18 \cdot (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) - 81 \cdot (\operatorname{\mathit{HardinA229582Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229582` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229582","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229582: one-defect three-colour width-4 sheared strips*. URL: <https://oeis.org/A229582>.

*Commentary.*

All natural counts in this equality are cast to integers. Relabelling the three colours gives six labelled arrays for each canonical array once at least two colours occur. The transfer relation then yields this recurrence with the displayed index shifts.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.Boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.antidiagonal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.cross`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
