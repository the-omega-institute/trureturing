# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Definition 1.1 (Rows).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

A row lists its colours in column order.

**Definition 1.2 (Outgoing boundary).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}} = (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

The tail of a row meets the following row along antidiagonal bonds.

**Definition 1.3 (Horizontal bonds).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.4 (Antidiagonal bonds).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.antidiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.5 (Retaining the outgoing tail).**

$$\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(r\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Column zero does not meet the next row.

**Definition 1.6 (Defects between rows).**

$$\forall p: \mathit{Boundary}, (\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(0, p\right), r\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.cross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

The inserted zero is outside every antidiagonal bond.

**Definition 1.7 (Admissible residual budgets).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 1) \land (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(3\right) \mapsto (p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le 1 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget.

**Definition 1.8 (Colour permutation classes).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 3 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 5 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 6 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 7 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 8 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 9 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 10 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 11 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 12 \operatorname{\mathit{else}} 13)))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Only equality relations between boundary colours affect continuation counts. The classes also record the remaining defect budget.

**Definition 1.9 (Class transfer matrix).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{T} = ![![5, 5, 3, 3, 1, 1, 5, 3, 3, 2, 2, 5, 5, 3], ![4, 4, 3, 3, 2, 2, 4, 2, 2, 3, 3, 6, 6, 3], ![2, 2, 3, 3, 4, 4, 2, 7, 7, 3, 3, 6, 6, 3], ![4, 4, 3, 3, 2, 2, 4, 6, 6, 1, 1, 4, 4, 3], ![0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 4, 4, 0], ![0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

**Definition 1.10 (Initial labelled row counts).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{initial}} = ![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

**Definition 1.11 (Terminal acceptance weights).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{terminal}} = ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

**Definition 1.12 (Forward transfer table).**

$$\operatorname{\mathit{HardinA229583StripData}}.\operatorname{W} = ![![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12], ![180, 180, 144, 144, 108, 108, 180, 438, 438, 108, 108, 516, 516, 144], ![2484, 2484, 1944, 1944, 1404, 1404, 2484, 11142, 11142, 1476, 1476, 11232, 11232, 1944], ![34020, 34020, 26568, 26568, 19116, 19116, 34020, 223182, 223182, 20196, 20196, 209304, 209304, 26568], ![465588, 465588, 363528, 363528, 261468, 261468, 465588, 4023270, 4023270, 276372, 276372, 3621672, 3621672, 363528], ![6371460, 6371460, 4974696, 4974696, 3577932, 3577932, 6371460, 68322366, 68322366, 3782052, 3782052, 59919912, 59919912, 4974696]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229583: one-defect three-colour width-5 sheared strips*. URL: <https://oeis.org/A229583>.

*Commentary.*

Finite vectors use Lean's ![...] notation. Matrix rows and vector entries are listed in increasing index order.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.Boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.antidiagonal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.cross`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
