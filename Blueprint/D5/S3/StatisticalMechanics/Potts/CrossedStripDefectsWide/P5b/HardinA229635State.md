# Boundary states

## Abstract

A previous row and remaining defect budget determine the transfer state.

**Definition 1.1 (Transfer indices).**

$$\operatorname{\mathit{State}} = \operatorname{\mathit{Fin}}\left(127\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The index type has 127 elements.

**Definition 1.2 (Fresh-state indices).**

$$\operatorname{\mathit{Fresh}} = \operatorname{\mathit{Fin}}\left(96\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.Fresh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The index type has 96 elements.

**Definition 1.3 (Labelled row indices).**

$$\operatorname{\mathit{RowNumber}} = \operatorname{\mathit{Fin}}\left(729\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.RowNumber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The index type has 729 elements.

**Definition 1.4 (Horizontal defects in a row).**

$$\forall p: \operatorname{\mathit{Row}}, (\operatorname{h}\left(p\right) = \operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{horizontal}}, p, p\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.h` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The count includes each monochromatic horizontal bond once.

**Definition 1.5 (Defect cost of adding a row).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall r: \operatorname{\mathit{Row}}, (\operatorname{\mathit{cost}}\left(p, r\right) = \operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{between}}, p, r\right) + \operatorname{h}\left(r\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Adding a row pays for both adjacent-row diagonals and all horizontal defects of the new row.

**Definition 1.6 (Validity of a row and budget).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (\operatorname{h}\left(p\right) + d \le 2)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

A boundary row and its remaining defect budget must fit within the total allowance of two.

**Definition 1.7 (Decidability of a boundary state).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{instDecidableValid}}\left(p, d\right) = \operatorname{\mathit{inferInstanceAs}}\left(\operatorname{\mathit{Decidable}}\left(\operatorname{h}\left(p\right) + d \le 2\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.instDecidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The validity test is the natural-number comparison of the horizontal defects plus the remaining budget with two.

**Definition 1.8 (Numbering of labelled rows).**

$$\operatorname{\mathit{rowEquiv}} = \operatorname{\mathit{Equiv}}.\operatorname{\mathit{symm}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(3, 6\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.rowEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The inverse of the base-three finite-function equivalence enumerates the six entries of every labelled row.

**Definition 1.9 (Representative of a fresh state).**

$$\forall i: \operatorname{\mathit{Fresh}}, (\operatorname{\mathit{rep}}\left(i\right) = \operatorname{\mathit{rowEquiv}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{ofNat}}\left(729, \operatorname{\mathit{Option}}.\operatorname{\mathit{getD}}\left(\operatorname{\mathit{Array}}.\operatorname{\mathit{getElemOptional}}\left(\operatorname{\mathit{representativeNumbers}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right), 0\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.rep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The table gives row numbers for the 96 canonical equality patterns with at most two horizontal defects.

**Definition 1.10 (Remaining budget of a fresh state).**

$$\forall i: \operatorname{\mathit{Fresh}}, (\operatorname{\mathit{budget}}\left(i\right) = 2 - \operatorname{h}\left(\operatorname{\mathit{rep}}\left(i\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.budget` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The remaining budget is the total allowance less the representative row's horizontal defects.

**Definition 1.11 (Index of the equality pattern).**

$$\forall p: \operatorname{\mathit{Row}}, (\operatorname{\mathit{fresh}}\left(p\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{ofNat}}\left(96, \operatorname{\mathit{List}}.\operatorname{\mathit{idxOf}}\left(\operatorname{\mathit{rowCode}}\left(p\right), \operatorname{\mathit{representativeCodes}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.fresh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The row code records equality for each pair of columns. The search locates that code in the fresh pattern table.

**Definition 1.12 (Transfer class of a boundary state).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} \operatorname{h}\left(p\right) + d \le 1 \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, \operatorname{\mathit{HardinA229532StripData}}.\operatorname{\mathit{cl}}\left(p, d\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(31, \operatorname{\mathit{fresh}}\left(p\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The 31 inherited states cover rows and budgets with sum at most one. All other valid states use the fresh pattern index after that block.

**Definition 1.13 (Destination of a candidate successor).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\forall r: \operatorname{\mathit{Row}}, (\operatorname{\mathit{destination}}\left(p, d, r\right) = (\operatorname{\mathit{if}} \operatorname{\mathit{cost}}\left(p, r\right) \le d \operatorname{\mathit{then}} \operatorname{\mathit{some}}\left(\operatorname{\mathit{cl}}\left(r, d - \operatorname{\mathit{cost}}\left(p, r\right)\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{none}}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.destination` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The available budget guards the subtraction. A legal transition records the successor row with its updated budget.

**Definition 1.14 (Full weighted successor list).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{outgoing}}\left(p, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{filterMap}}\left(\operatorname{\mathit{destination}}\left(p, d\right), \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\operatorname{\mathit{rowEquiv}}\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.outgoing` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The list examines every labelled row and retains one class entry for each affordable move.

**Definition 1.15 (Class for a candidate first row).**

$$\forall p: \operatorname{\mathit{Row}}, (\operatorname{\mathit{startClass}}\left(p\right) = (\operatorname{\mathit{if}} \operatorname{h}\left(p\right) \le 2 \operatorname{\mathit{then}} \operatorname{\mathit{some}}\left(\operatorname{\mathit{cl}}\left(p, 2 - \operatorname{h}\left(p\right)\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{none}}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.startClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The first row uses only its horizontal defects and starts from allowance two.

**Definition 1.16 (List of allowed first-row classes).**

$$\operatorname{\mathit{startClasses}} = \operatorname{\mathit{List}}.\operatorname{\mathit{filterMap}}\left(\operatorname{\mathit{startClass}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\operatorname{\mathit{rowEquiv}}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.startClasses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Enumerating all labelled rows gives the initial class multiplicities.

**Theorem 1.17 (Filter-map multiplicities).**

$$\forall f: (\operatorname{\mathit{Row}}) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{State}}\right)), (\forall s: \operatorname{\mathit{State}}, ((\operatorname{\mathit{List}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{List}}.\operatorname{\mathit{filterMap}}\left(f, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\operatorname{\mathit{rowEquiv}}\right)\right)\right): \int) = \sum_{r: \operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} f\left(r\right) = \operatorname{\mathit{some}}\left(s\right) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.count_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Filtering a complete list of rows and counting an output class agrees with summing its indicator over all rows.

**Theorem 1.18 (Entry of the weighted successor vector).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\forall s: \operatorname{\mathit{State}}, ((\operatorname{\mathit{List}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{outgoing}}\left(p, d\right)\right): \int) = \sum_{r: \operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} (\operatorname{\mathit{cost}}\left(p, r\right) \le d) \land (\operatorname{\mathit{cl}}\left(r, d - \operatorname{\mathit{cost}}\left(p, r\right)\right) = s) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.outgoing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The indicator imposes both affordability and the destination class after payment.

**Theorem 1.19 (Entry of the first-row vector).**

$$\forall s: \operatorname{\mathit{State}}, ((\operatorname{\mathit{List}}.\operatorname{\mathit{count}}\left(s, \operatorname{\mathit{startClasses}}\right): \int) = \sum_{r: \operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} (\operatorname{h}\left(r\right) \le 2) \land (\operatorname{\mathit{cl}}\left(r, 2 - \operatorname{h}\left(r\right)\right) = s) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.start_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The indicator enforces the two-defect allowance and the class of the resulting first row.

**Theorem 1.20 (Horizontal cost is relabelling invariant).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{Row}}, (\operatorname{h}\left((e) \circ (p)\right) = \operatorname{h}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.h_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

A common colour permutation preserves endpoint equality.

**Theorem 1.21 (Transition cost is relabelling invariant).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{Row}}, (\forall r: \operatorname{\mathit{Row}}, (\operatorname{\mathit{cost}}\left((e) \circ (p), (e) \circ (r)\right) = \operatorname{\mathit{cost}}\left(p, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cost_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The same permutation acts on both rows and preserves all three types of bond defects.

**Theorem 1.22 (Class is relabelling invariant).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{cl}}\left((e) \circ (p), d\right) = \operatorname{\mathit{cl}}\left(p, d\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cl_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Both the inherited and fresh class maps depend on equality patterns and the remaining budget.

**Theorem 1.23 (Closure of valid states).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, (\forall r: \operatorname{\mathit{Row}}, ((\operatorname{\mathit{Valid}}\left(p, d\right)) \implies ((\operatorname{\mathit{cost}}\left(p, r\right) \le d) \implies (\operatorname{\mathit{Valid}}\left(r, d - \operatorname{\mathit{cost}}\left(p, r\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

After an affordable move the new horizontal cost plus the new budget is at most the old budget.

**Theorem 1.24 (Closure of the inherited block).**

$$\forall p: \operatorname{\mathit{Row}}, (\forall r: \operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{h}\left(p\right) + d \le 1) \implies ((\operatorname{\mathit{cost}}\left(p, r\right) \le d) \implies (\operatorname{h}\left(r\right) + d - \operatorname{\mathit{cost}}\left(p, r\right) \le 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

A transition from the one-defect sector stays in the inherited block.

**Theorem 1.25 (Validity of an allowed first row).**

$$\forall r: \operatorname{\mathit{Row}}, ((\operatorname{h}\left(r\right) \le 2) \implies (\operatorname{\mathit{Valid}}\left(r, 2 - \operatorname{h}\left(r\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.legal_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

First-row payment leaves budget two minus the horizontal cost.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.Fresh`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.RowNumber`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.State`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.budget`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cl_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.closed`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.cost_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.count_classes`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.destination`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.fresh`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.h`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.h_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.instDecidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.legal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.legal_start`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.outgoing`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.outgoing_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.rep`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.rowEquiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.startClass`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.startClasses`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State.start_count`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData](../WidthSix/HardinA229532StripData.md)
