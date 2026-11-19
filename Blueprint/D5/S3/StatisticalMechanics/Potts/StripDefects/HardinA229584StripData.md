# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Definition 1.1 (Rows).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

A row lists its colours in column order.

**Definition 1.2 (Outgoing boundary).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Boundary}} = (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The tail of a row meets the following row along antidiagonal bonds.

**Definition 1.3 (Horizontal bonds).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.4 (Antidiagonal bonds).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{antidiagonal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.antidiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.5 (Retaining the outgoing tail).**

$$\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(r\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Column zero does not meet the next row.

**Definition 1.6 (Defects between rows).**

$$\forall p: \mathit{Boundary}, (\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(0, p\right), r\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.cross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The inserted zero is outside every antidiagonal bond.

**Definition 1.7 (Admissible residual budgets).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 1) \land (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto (p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le 1 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget.

**Definition 1.8 (Colour permutation classes).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (d = 1) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} 2) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 3)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} 5) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 6 \operatorname{\mathit{else}} 7))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} 12 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 20 \operatorname{\mathit{else}} 25)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(2\right) = p\left(4\right)) \operatorname{\mathit{then}} 8 \operatorname{\mathit{else}} 9) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} 13 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 24 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 21 \operatorname{\mathit{else}} 26))))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 14 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 15 \operatorname{\mathit{else}} 16)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 17 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 18 \operatorname{\mathit{else}} 19))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 10 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 22 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 27 \operatorname{\mathit{else}} 30))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 28 \operatorname{\mathit{else}} 29) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 11 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 23 \operatorname{\mathit{else}} 31)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Only equality relations between boundary colours affect continuation counts. The classes also record the remaining defect budget.

**Definition 1.9 (Class transfer matrix).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{T} = ![![5, 5, 4, 4, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4, 0, 0, 2, 2, 1, 5, 5, 5, 3, 5, 2, 2], ![3, 3, 3, 3, 2, 2, 3, 3, 0, 0, 1, 1, 4, 4, 5, 3, 5, 5, 5, 3, 2, 2, 2, 2, 2, 4, 4, 2, 3, 2, 1, 1], ![4, 4, 4, 4, 1, 1, 3, 3, 2, 2, 1, 1, 0, 0, 2, 4, 2, 0, 0, 4, 1, 1, 2, 2, 1, 6, 6, 5, 3, 5, 2, 2], ![2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4, 4, 3, 2, 3, 4, 4, 2, 3, 3, 3, 3, 3, 5, 5, 3, 2, 3, 1, 1], ![1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2, 2, 2, 2, 4, 1, 4, 6, 6, 1, 3, 3, 3, 3, 3, 5, 5, 7, 1, 7, 2, 2], ![2, 2, 2, 2, 2, 2, 3, 3, 4, 4, 2, 2, 0, 0, 7, 2, 7, 4, 4, 2, 2, 2, 1, 1, 2, 4, 4, 4, 3, 4, 1, 1], ![3, 3, 3, 3, 1, 1, 3, 3, 0, 0, 2, 2, 2, 2, 5, 3, 5, 5, 5, 3, 1, 1, 1, 1, 1, 6, 6, 2, 3, 2, 2, 2], ![4, 4, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 4, 4, 4, 8, 8, 2, 0, 0, 1, 1, 2, 2, 2, 4, 3, 4, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 4, 4, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 4, 4, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 5, 4, 4, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 3, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 3, 3, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 3, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

**Definition 1.10 (Initial labelled row counts).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}} = ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 6, 6, 6, 12, 12, 12, 12, 12, 12, 6, 6, 6, 12, 6, 12, 12]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

**Definition 1.11 (Terminal acceptance weights).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{terminal}} = ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

**Definition 1.12 (Forward transfer table).**

$$\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W} = ![![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 6, 6, 6, 12, 12, 12, 12, 12, 12, 6, 6, 6, 12, 6, 12, 12], ![288, 288, 252, 252, 180, 180, 252, 252, 180, 180, 144, 144, 180, 180, 804, 288, 804, 834, 834, 252, 144, 144, 180, 180, 180, 954, 954, 810, 252, 810, 144, 144], ![6120, 6120, 5328, 5328, 3528, 3528, 5220, 5220, 3240, 3240, 2808, 2808, 3816, 3816, 31812, 6120, 31812, 30540, 30540, 5328, 2736, 2736, 3636, 3636, 3528, 28500, 28500, 29442, 5220, 29442, 2916, 2916], ![128052, 128052, 111492, 111492, 72972, 72972, 108792, 108792, 66096, 66096, 57888, 57888, 79848, 79848, 970530, 128052, 970530, 904818, 904818, 111492, 56412, 56412, 75672, 75672, 72972, 769146, 769146, 873804, 108792, 873804, 60588, 60588], ![2673828, 2673828, 2328192, 2328192, 1521360, 1521360, 2270412, 2270412, 1375380, 1375380, 1206144, 1206144, 1667340, 1667340, 26634390, 2673828, 26634390, 24439764, 24439764, 2328192, 1175724, 1175724, 1579140, 1579140, 1521360, 19682196, 19682196, 23650482, 2270412, 23650482, 1263924, 1263924], ![55816740, 55816740, 48602088, 48602088, 31752288, 31752288, 47391840, 47391840, 28698300, 28698300, 25171128, 25171128, 34806276, 34806276, 688994430, 55816740, 688994430, 625991628, 625991628, 48602088, 24537636, 24537636, 32962536, 32962536, 31752288, 486524004, 486524004, 606623268, 47391840, 606623268, 26381376, 26381376], ![1165146192, 1165146192, 1014545772, 1014545772, 662795532, 662795532, 989271072, 989271072, 599027076, 599027076, 525414168, 525414168, 726563988, 726563988, 17158850556, 1165146192, 17158850556, 15484831014, 15484831014, 1014545772, 512195112, 512195112, 688070232, 688070232, 662795532, 11735324790, 11735324790, 15020284764, 989271072, 15020284764, 550688868, 550688868], ![24321728268, 24321728268, 21178039932, 21178039932, 13835412540, 13835412540, 20650414572, 20650414572, 12504235680, 12504235680, 10967650344, 10967650344, 15166589400, 15166589400, 416138142246, 24321728268, 416138142246, 373702732554, 373702732554, 21178039932, 10691724204, 10691724204, 14363037900, 14363037900, 13835412540, 277936960938, 277936960938, 362748285894, 20650414572, 362748285894, 11495275704, 11495275704]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.Boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.antidiagonal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.cross`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
