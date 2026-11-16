# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Definition 1.1 (Rows).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(7\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

A row lists its colours in column order.

**Definition 1.2 (Outgoing boundary).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}} = (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The tail of a row meets the following row along antidiagonal bonds.

**Definition 1.3 (Horizontal bonds).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.4 (Antidiagonal bonds).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(6\right) \mapsto ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.antidiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Each index specifies one bond, and each bond is counted once.

**Definition 1.5 (Retaining the outgoing tail).**

$$\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(r\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Column zero does not meet the next row.

**Definition 1.6 (Defects between rows).**

$$\forall p: \mathit{Boundary}, (\forall r: \mathit{Row}, (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(0, p\right), r\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.cross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The inserted zero is outside every antidiagonal bond.

**Definition 1.7 (Admissible residual budgets).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 1) \land (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le 1 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The remaining budget is zero or one. Equal consecutive boundary entries already consume part of the total budget.

**Definition 1.8 (Colour permutation classes).**

$$\forall p: \mathit{Boundary}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{HardinA233255ShapeSymmetry}}.\operatorname{\mathit{proper}}\left(p\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (d = 1) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA233255ShapeSymmetry}}.\operatorname{\mathit{classOf}}\left(p\right)\right)\right) \operatorname{\mathit{else}} ![29, 30, 33, 34, 37, 38, 39, 41, 54, 56, 57, 58, 61, 62, 65, 66]\left(\operatorname{\mathit{HardinA233255ShapeSymmetry}}.\operatorname{\mathit{classOf}}\left(p\right)\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (d = 1) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} 1) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} 5)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} 6) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 3 \operatorname{\mathit{else}} 7))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 8 \operatorname{\mathit{else}} 10) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 9 \operatorname{\mathit{else}} 11)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} 12 \operatorname{\mathit{else}} 13) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} 14 \operatorname{\mathit{else}} 15)))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(2\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 28 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 31 \operatorname{\mathit{else}} 33)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 24 \operatorname{\mathit{else}} 26) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 36 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 39 \operatorname{\mathit{else}} 42)))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 29 \operatorname{\mathit{else}} 37) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} 27 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 34 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 40 \operatorname{\mathit{else}} 43)))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 30 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 32 \operatorname{\mathit{else}} 35)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} 25 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 38 \operatorname{\mathit{else}} 41))))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(2\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 16 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 44 \operatorname{\mathit{else}} 57)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 17 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 45 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} 58 \operatorname{\mathit{else}} 59)))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 18 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 52 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 47 \operatorname{\mathit{else}} 55))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 46 \operatorname{\mathit{else}} 54) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 19 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} 53 \operatorname{\mathit{else}} 56))))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(2\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 20 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 48 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 62 \operatorname{\mathit{else}} 69))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} 60 \operatorname{\mathit{else}} 61) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 21 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 49 \operatorname{\mathit{else}} 68)))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(5\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 63 \operatorname{\mathit{else}} 65) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 22 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 50 \operatorname{\mathit{else}} 70))) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(4\right)) \operatorname{\mathit{then}} 64 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(5\right)) \operatorname{\mathit{then}} 66 \operatorname{\mathit{else}} 67)) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(1\right)) \operatorname{\mathit{then}} 23 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(2\right)) \operatorname{\mathit{then}} 51 \operatorname{\mathit{else}} 71)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Proper boundaries use HardinA233255ShapeSymmetry.classOf and its representatives/shapeEquiv ordering. Budget one includes its value in Fin 72; other budgets compose with the displayed injection m. The Fin.mk bound follows from the class lying in Fin 16. Nonproper inputs retain the displayed equality classifier, including invalid-budget behaviour.

**Definition 1.9 (Class transfer matrix).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(72\right), \operatorname{\mathit{Fin}}\left(72\right), \mathit{Int}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

This 72 by 72 integer matrix uses source and destination indices in Fin 72, in cl order. Its leading 16 by 16 block is HardinA233255Recurrence.table through the inclusion i ↦ i. The zero-budget block uses the same owner table through zeroBudgetClass on both indices, with zero entries outside that column image in its rows. The other entries remain the literal transition weights in the Lean owner. HardinA233255Recurrence.table_matches pins the delegated table to K. HardinA229585StripOrbitTable.table_counts pins every T entry to the count of the destination class in images, and HardinA229585StripOrbitCertificate.transition_counts identifies those multiplicities with actual permitted rows.

**Definition 1.10 (Initial labelled row counts).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{initial}} = ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 6, 6, 6, 12, 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 6, 6, 6, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 12, 12, 12]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Finite vectors are displayed in index order using Lean vector notation ![...].

**Definition 1.11 (Terminal acceptance weights).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{terminal}} = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

Finite vectors are displayed in index order using Lean vector notation ![...].

**Definition 1.12 (Forward transfer table).**

$$\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}: (\operatorname{\mathit{Fin}}\left(11\right)) \to ((\operatorname{\mathit{Fin}}\left(72\right)) \to (\mathit{Int}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The eleven integer vectors are indexed by Fin 11; each has 72 coordinates in cl order. Entries are the finite row vectors in the Lean definition. HardinA229585StripCertificate.structural_certificate pins W 0 to initial, each of the ten following vectors to Matrix.vecMul of its predecessor with T, and W 10 to the stated linear combination of W 2 through W 9. The five ForwardChecks.forward_steps theorems check those ten successive transfer steps.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.Boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.antidiagonal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.cross`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255Recurrence](../../../Combinatorics/TraceAvoidingArrays/HardinA233255Recurrence.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
