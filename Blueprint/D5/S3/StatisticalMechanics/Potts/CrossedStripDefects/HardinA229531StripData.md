# Width-five HDA transfer

## Abstract

Exact width-five HDA transfer.

**Theorem 1.1 (Proper successors from the frozen scanner certificate).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(p\right)) \implies (\forall j: \operatorname{\mathit{Fin}}\left(7\right), (32 \cdot (\sum_{q: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(q\right)) \land ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{compatible}}\left(\operatorname{\mathit{true}}, p, q\right)) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), q\right) = j))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}}))) = \operatorname{\mathit{HardinA233171DiagonalStrip}}.\operatorname{\mathit{transfer}}\left(\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right), j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.raw_successors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

For every proper source row and every Fin 7 target class, thirty-two times the raw proper successor sum equals the corresponding frozen transfer entry. The proof applies the original class_fibres and finite_certificate and pushes saturated Seen fibres with weight 32. Each consumed target-class theorem supplies its own exact bond, budget and class correspondence before integer division.

**Definition 1.2 (Actual rows).**

$$\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

Row is the function type Fin 5 to Fin 3. Its 243 values are the actual labelled rows.

**Definition 1.3 (Horizontal bonds).**

$$\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The horizontal bond set is HardinA229583StripData.horizontal, containing the four adjacent pairs in Fin 5.

**Definition 1.4 (Crossed bonds).**

$$\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{between}} = \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}} \cup \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{swap}}, \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The inter-row bond set is the union of HardinA229583StripData.antidiagonal with its coordinate-swapped image, containing both diagonals for each adjacent column pair.

**Definition 1.5 (Valid residual states).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right) = ((d \le 1) \land (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 1 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

Valid p d means that d is at most one and the internal horizontal defect count of p is at most one minus d.

**Definition 1.6 (Finite state decision).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{decidableValid}}\left(p, d\right): \operatorname{\mathit{Decidable}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.decidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The instance decides the conjunction defining Valid on an actual row and natural residual budget.

**Definition 1.7 (The class map).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{cl}}\left(p, d\right): \operatorname{\mathit{Fin}}\left(20\right)) = (\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 1))) \operatorname{\mathit{then}} (0) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 2))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 3))) \operatorname{\mathit{then}} (2) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 4))) \operatorname{\mathit{then}} (3) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 5))) \operatorname{\mathit{then}} (4) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 6))) \operatorname{\mathit{then}} (5) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 1))) \operatorname{\mathit{then}} (6) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 2))) \operatorname{\mathit{then}} (7) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 3))) \operatorname{\mathit{then}} (8) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 4))) \operatorname{\mathit{then}} (9) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 5))) \operatorname{\mathit{then}} (10) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinA233126SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 6))) \operatorname{\mathit{then}} (11) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) = p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) = p\left(4\right))))))))))))) \operatorname{\mathit{then}} (12) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) = p\left(4\right))))))))))))) \operatorname{\mathit{then}} (13) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) = p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) = p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) = p\left(4\right))))))))))))) \operatorname{\mathit{then}} (14) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) = p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) = p\left(4\right))))))))))))) \operatorname{\mathit{then}} (15) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) = p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) = p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))))) \operatorname{\mathit{then}} (16) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) = p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) = p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))))) \operatorname{\mathit{then}} (17) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(4\right)) \land ((p\left(2\right) \ne p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(0\right) \ne p\left(4\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land ((p\left(1\right) = p\left(4\right)) \land ((p\left(2\right) = p\left(3\right)) \land ((p\left(2\right) \ne p\left(4\right)) \land (p\left(3\right) \ne p\left(4\right))))))))))))) \operatorname{\mathit{then}} (18) \operatorname{\mathit{else}} (19))))))))))))))))))))))))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The map Row times Nat to Fin 20 identifies global colour permutations and reflection. Proper rows use HardinA233126SquareStrip.boundaryClass at Seen=(true,true); defective rows use their full equality pattern. The transition_counts theorems pin the class transfer for every valid state.

**Definition 1.8 (The transfer matrix).**

$$(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(20\right), \operatorname{\mathit{Fin}}\left(20\right), \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

T is an integer matrix indexed by Fin 20 on both axes. Its proper-row diagonal subblocks call HardinA233171DiagonalStrip.transfer at indices one through six and divide by 32. The division removes the two lifts per colour in each of five cells after Seen is saturated. Every entry is pinned to the actual three-colour successor sum by HardinA229531StripClasses.transition_counts.

**Definition 1.9 (Initial distribution).**

$$(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{initial}}: (\operatorname{\mathit{Fin}}\left(20\right)) \to (\operatorname{\mathit{Int}}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The vector Fin 20 to Int counts first rows by their exact residual budget and class. HardinA229531Strip.finite_certificate verifies these weights.

**Definition 1.10 (Terminal acceptance).**

$$(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{\mathit{terminal}}: (\operatorname{\mathit{Fin}}\left(20\right)) \to (\operatorname{\mathit{Int}}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The vector Fin 20 to Int is one exactly at zero-residual classes and zero otherwise; HardinA229531Strip.finite_certificate checks this for all valid rows.

**Definition 1.11 (Forward weights).**

$$(\operatorname{\mathit{HardinA229531StripData}}.\operatorname{W}: (\operatorname{\mathit{Fin}}\left(14\right)) \to ((\operatorname{\mathit{Fin}}\left(20\right)) \to (\operatorname{\mathit{Int}})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

W has type Fin 14 to Fin 20 to Int. Its fourteen rows are the initial vector followed by thirteen right multiplications by T. HardinA229531Strip.finite_certificate pins those identities and the order-twelve polynomial relation.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.decidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.raw_successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](../../../Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](../../../Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData](../StripDefects/HardinA229583StripData.md)
