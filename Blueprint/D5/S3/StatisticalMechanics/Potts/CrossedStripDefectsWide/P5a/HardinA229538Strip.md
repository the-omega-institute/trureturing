# Canonical one-defect colourings of five-row HDA arrays

## Abstract

Canonical one-defect colourings of five-row HDA arrays

Colours are introduced in row-major order. At the widths used in the recurrence, each canonical array has six distinct label permutations.

**Definition 1.1 (canonicalCount).**

$$\forall (D: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(D, n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right))\mapsto ((\operatorname{DefectTransfer}.\operatorname{defects}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), \operatorname{Finset}.\operatorname{filter}\left((\lambda ((r, s): (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right)))\mapsto (\operatorname{Fin}.\operatorname{val}\left(s\right) = \operatorname{Fin}.\operatorname{val}\left(r\right) \lor \left(\operatorname{Fin}.\operatorname{val}\left(s\right) = (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) \lor \operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right))\right), \operatorname{List}.\operatorname{ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right))\mapsto ((\lambda (i: \operatorname{Fin}\left(5\right))\mapsto (A\left((i, j)\right)))))\right)\right) = D) \land (\forall (p: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right))), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = c)))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.canonicalCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The filter counts five-by-n arrays with exactly D monochromatic bonds and row-major canonical colour introduction.

**Definition 1.2 (a).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229538Strip}.\operatorname{a}\left(n\right): \operatorname{Nat}) = \operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(1, n\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The column-sweep count uses defect budget one.

**Definition 1.3 (residual).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (d: \operatorname{Nat}), ((\operatorname{HardinA229538Strip}.\operatorname{residual}\left(p, d\right): \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)) = (\operatorname{if} (d = 0) \operatorname{then} \operatorname{Sum}.\operatorname{inr}\left(p\right) \operatorname{else} \operatorname{Sum}.\operatorname{inl}\left(p\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Budgets zero and one select the right and left summands respectively.

**Theorem 1.4 (transition_entry).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (d: \operatorname{Nat}), ((d \le 1) \Rightarrow (\forall (s: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)), (((\operatorname{if} ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) \le d) \land (\operatorname{HardinA229538Strip}.\operatorname{residual}\left(q, (d) - (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right))\right) = s)) \operatorname{then} 1 \operatorname{else} 0): \operatorname{Int}) = (\operatorname{if} (\operatorname{Sum}.\operatorname{elim}\left(\operatorname{id}, \operatorname{id}, s\right) = q) \operatorname{then} \operatorname{HardinA229538Strip}.\operatorname{transfer}\left(\operatorname{HardinA229538Strip}.\operatorname{residual}\left(p, d\right), s\right) \operatorname{else} 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transition_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

A successor entry has the value one only for the column and residual budget produced by the cut.

**Theorem 1.5 (labelled_scale).**

$$\forall (D: \operatorname{Nat}), (\forall (m: \operatorname{Nat}), ((1 \le m) \Rightarrow ((D < 3) \Rightarrow (\left(\operatorname{DefectTransfer}.\operatorname{literalCount}_{3}\right)\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), \operatorname{Finset}.\operatorname{filter}\left((\lambda ((r, s): (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right)))\mapsto (\operatorname{Fin}.\operatorname{val}\left(s\right) = \operatorname{Fin}.\operatorname{val}\left(r\right) \lor \left(\operatorname{Fin}.\operatorname{val}\left(s\right) = (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) \lor \operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right))\right), D, (m) + (1)\right) = (6) \cdot (\operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(D, (m) + (1)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.labelled_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

At widths at least two and with fewer than three defects, each canonical array has six labelled representatives. The subscript on literalCount gives the palette size.

Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.

**Definition 1.6 (edges).**

$$(\operatorname{HardinA229538Strip}.\operatorname{edges}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)) = \operatorname{Finset}.\operatorname{filter}\left((\lambda ((r, s): (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right)))\mapsto (\operatorname{Fin}.\operatorname{val}\left(s\right) = \operatorname{Fin}.\operatorname{val}\left(r\right) \lor \left(\operatorname{Fin}.\operatorname{val}\left(s\right) = (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) \lor \operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The oriented cut is the set of pairs of row indices that form a bond between columns zero and one.

**Definition 1.7 (cost).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right): \operatorname{Nat}) = \operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229538Strip}.\operatorname{edges}, \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(q\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The cost is the number of monochromatic bonds on the cut between two decoded columns.

**Theorem 1.8 (bondDefects_empty).**

$$\forall (r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), r, r\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.bondDefects_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The number of monochromatic bonds of a row against itself over the empty edge set is zero.

**Theorem 1.9 (cost_zero).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 0) \Leftrightarrow (\operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

A cut has cost zero exactly when every bond has different colours at its endpoints.

**Theorem 1.10 (zero_cost_entry).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{if} (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 0) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0) = \operatorname{HardinA233178Chromatic}.\operatorname{T}\left(p, q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_cost_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The proper-colouring transfer entry is the indicator of a cut without monochromatic bonds.

**Definition 1.11 (oneDefect).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{oneDefect}\left(p, q\right): \operatorname{Int}) = (\operatorname{if} (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 1) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.oneDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Each entry is the indicator of a cut with exactly one monochromatic bond.

**Definition 1.12 (transfer).**

$$(\operatorname{HardinA229538Strip}.\operatorname{transfer}: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{Int}\right)) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233178Chromatic}.\operatorname{T}, \operatorname{HardinA229538Strip}.\operatorname{oneDefect}, (0: \operatorname{Matrix}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Int}\right)), \operatorname{HardinA233178Chromatic}.\operatorname{T}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The two summands represent one and zero residual defects. A zero-cost cut preserves the budget and a cut of cost one moves from the first summand to the second.

**Definition 1.13 (terminal).**

$$(\operatorname{HardinA229538Strip}.\operatorname{terminal}: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left((0: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The empty continuation completes an array exactly when its remaining budget is zero.

**Theorem 1.14 (transfer_readout).**

$$\forall (S: \operatorname{Type}*), ([\operatorname{Fintype}\left(S\right)] [\operatorname{DecidableEq}\left(S\right)] \forall (M: \operatorname{Matrix}\left(S, S, \operatorname{Int}\right)), (\forall (u: S \to \operatorname{Int}), (\forall (v: S \to \operatorname{Int}), (\forall (d: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Fin}\left(d\right) \to \operatorname{Int}), ((\operatorname{Matrix}.\operatorname{mulVec}\left((M)^{(b) + (d)}, u\right) = \sum_{(j: \operatorname{Fin}\left(d\right))} (\operatorname{SMul}.\operatorname{smul}\left(c\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left((M)^{(b) + (\operatorname{Fin}.\operatorname{val}\left(j\right))}, u\right)\right))) \Rightarrow (\forall (n: \operatorname{Nat}), (\operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left((M)^{((n) + (b)) + (d)}, u\right)\right) = \sum_{(j: \operatorname{Fin}\left(d\right))} ((c\left(j\right)) \cdot (\operatorname{dotProduct}\left(v, \operatorname{Matrix}.\operatorname{mulVec}\left((M)^{((n) + (b)) + (\operatorname{Fin}.\operatorname{val}\left(j\right))}, u\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transfer_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The state type belongs to an arbitrary universe. A vector recurrence for a matrix and terminal vector gives a shifted scalar recurrence for every readout vector.

**Definition 1.15 (countCut).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{countCut}\left(p, q\right): \operatorname{Nat}) = (((((((((((((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 0\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 0\right)) \operatorname{then} 1 \operatorname{else} 0)) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 0\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 1\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 1\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 0\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 1\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 1\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 1\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 2\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 2\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 1\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 2\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 2\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 2\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 3\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 3\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 2\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 3\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 3\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 3\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 4\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 4\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 3\right)) \operatorname{then} 1 \operatorname{else} 0))) + ((\operatorname{if} (\operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(p, 4\right) = \operatorname{HardinA233178Chromatic}.\operatorname{colour}\left(q, 4\right)) \operatorname{then} 1 \operatorname{else} 0))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.countCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The cost counts the colour coincidences at the thirteen oriented pairs of row positions.

**Theorem 1.16 (cost_countCut).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = \operatorname{HardinA229538Strip}.\operatorname{countCut}\left(p, q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost_countCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The sum of the thirteen indicators equals the number of monochromatic bonds on the cut.

**Definition 1.17 (movesOne).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{movesOne}\left(p\right): \operatorname{List}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)) = \operatorname{List}.\operatorname{filter}\left((\lambda (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column})\mapsto \operatorname{decide}\left(\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 1\right)), \operatorname{List}.\operatorname{finRange}\left(243\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.movesOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The list consists of the successor columns with cut cost one, in increasing column-code order.

**Theorem 1.18 (step_one).**

$$\forall (w: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229538Strip}.\operatorname{oneDefect}, w\right)\left(p\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(w, \operatorname{HardinA229538Strip}.\operatorname{movesOne}\left(p\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.step_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The action of the exact-one-cut matrix is a sum over its successors.

**Definition 1.19 (weights).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\forall (j: \operatorname{Fin}\left(12\right)), ((\operatorname{HardinA229538Strip}.\operatorname{weights}\left(n, j\right): \operatorname{Int}) = (\operatorname{if} ((h: \operatorname{Fin}.\operatorname{val}\left(n\right) < 12)) \operatorname{then} (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), \operatorname{Int}\right))\left(\operatorname{Fin}.\operatorname{castLT}\left(n, h\right), j\right) \operatorname{else} (\operatorname{if} (\operatorname{Fin}.\operatorname{val}\left(n\right) = 12) \operatorname{then} \operatorname{Fin}.\operatorname{append}\left((0: \operatorname{Fin}\left(2\right) \to \operatorname{Int}), \operatorname{HardinA233178Chromatic}.\operatorname{coefficients}\right)\left(j\right) \operatorname{else} \sum_{(k: \operatorname{Fin}\left(10\right))} ((\operatorname{HardinA233178Chromatic}.\operatorname{coefficients}\left(k\right)) \cdot (\operatorname{HardinA229538Strip}.\operatorname{weights}\left(\operatorname{Fin}.\operatorname{ofNat}\left(23, (\operatorname{Fin}.\operatorname{val}\left(n\right) - 10) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right), j\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The identity selects the first twelve rows. The row at exponent twelve appends the proper-colouring coefficients to two zeros. The remaining rows are stored in a lookup of shape Fin 10 × Fin 12 and satisfy the displayed recurrence. Each recursive exponent is strictly below the current exponent and below 23.

**Definition 1.20 (classIndex).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{classIndex}\left(p\right): \operatorname{Fin}\left(25\right)) = (\operatorname{Matrix}.\operatorname{vecCons}\left(0, \operatorname{Matrix}.\operatorname{vecCons}\left(1, \operatorname{Matrix}.\operatorname{vecCons}\left(2, \operatorname{Matrix}.\operatorname{vecCons}\left(3, \operatorname{Matrix}.\operatorname{vecCons}\left(4, \operatorname{Matrix}.\operatorname{vecCons}\left(5, \operatorname{Matrix}.\operatorname{vecCons}\left(6, \operatorname{Matrix}.\operatorname{vecCons}\left(7, \operatorname{Matrix}.\operatorname{vecCons}\left(8, \operatorname{Matrix}.\operatorname{vecCons}\left(3, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecCons}\left(10, \operatorname{Matrix}.\operatorname{vecCons}\left(11, \operatorname{Matrix}.\operatorname{vecCons}\left(12, \operatorname{Matrix}.\operatorname{vecCons}\left(2, \operatorname{Matrix}.\operatorname{vecCons}\left(13, \operatorname{Matrix}.\operatorname{vecCons}\left(14, \operatorname{Matrix}.\operatorname{vecCons}\left(15, \operatorname{Matrix}.\operatorname{vecCons}\left(6, \operatorname{Matrix}.\operatorname{vecCons}\left(16, \operatorname{Matrix}.\operatorname{vecCons}\left(17, \operatorname{Matrix}.\operatorname{vecCons}\left(18, \operatorname{Matrix}.\operatorname{vecCons}\left(11, \operatorname{Matrix}.\operatorname{vecCons}\left(8, \operatorname{Matrix}.\operatorname{vecCons}\left(13, \operatorname{Matrix}.\operatorname{vecCons}\left(19, \operatorname{Matrix}.\operatorname{vecCons}\left(20, \operatorname{Matrix}.\operatorname{vecCons}\left(1, \operatorname{Matrix}.\operatorname{vecCons}\left(21, \operatorname{Matrix}.\operatorname{vecCons}\left(22, \operatorname{Matrix}.\operatorname{vecCons}\left(14, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecCons}\left(10, \operatorname{Matrix}.\operatorname{vecCons}\left(23, \operatorname{Matrix}.\operatorname{vecCons}\left(18, \operatorname{Matrix}.\operatorname{vecCons}\left(24, \operatorname{Matrix}.\operatorname{vecCons}\left(7, \operatorname{Matrix}.\operatorname{vecCons}\left(16, \operatorname{Matrix}.\operatorname{vecCons}\left(22, \operatorname{Matrix}.\operatorname{vecCons}\left(19, \operatorname{Matrix}.\operatorname{vecCons}\left(4, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right): \operatorname{Fin}\left(41\right) \to \operatorname{Fin}\left(25\right))\left(\operatorname{HardinA233260Literal}.\operatorname{cls}\left((\operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(0\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(1\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(2\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(3\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(4\right))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.classIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The lookup classifies five-entry boundary columns under colour permutation and row reversal.

**Definition 1.21 (tableOne).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{tableOne}\left(n, p\right): \operatorname{Int}) = \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right)\left(\operatorname{Sum}.\operatorname{inl}\left(p\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.tableOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The stored lookup has shape Fin 23 × Fin 25, with row n and column classIndex(p). The displayed entry is the left-summand projection of the continuation vector at exponent n.

**Definition 1.22 (zeroValues).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{zeroValues}\left(n, p\right): \operatorname{Int}) = (\operatorname{if} ((h: \operatorname{Fin}.\operatorname{val}\left(n\right) < 12)) \operatorname{then} \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(\operatorname{Fin}.\operatorname{castLT}\left(n, h\right), p\right) \operatorname{else} \sum_{(j: \operatorname{Fin}\left(12\right))} ((\operatorname{HardinA229538Strip}.\operatorname{weights}\left(n, j\right)) \cdot (\operatorname{HardinA233178Chromatic}.\operatorname{table}\left(j, p\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zeroValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

For larger exponents the zero-defect values are linear combinations of the twelve proper-colouring vectors.

**Theorem 1.23 (weight_eq).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538Strip}.\operatorname{zeroValues}\left(n\right) = \sum_{(j: \operatorname{Fin}\left(12\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229538Strip}.\operatorname{weights}\left(n, j\right), \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weight_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The same coefficient formula also holds at the tabulated exponents.

**Theorem 1.24 (zero_values).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538Strip}.\operatorname{zeroValues}\left(n\right) = \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The reconstructed value is the proper-colouring continuation vector at each exponent.

**Theorem 1.25 (table_powers).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{HardinA229538Strip}.\operatorname{tableOne}\left(n\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.table_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The first coordinate gives the one-defect continuations and the second gives the inherited proper-colouring continuations.

**Definition 1.26 (coefficients538).**

$$(\operatorname{HardinA229538Strip}.\operatorname{coefficients538}: \operatorname{Fin}\left(20\right) \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{vecCons}\left((-1296), \operatorname{Matrix}.\operatorname{vecCons}\left(5184, \operatorname{Matrix}.\operatorname{vecCons}\left(8640, \operatorname{Matrix}.\operatorname{vecCons}\left((-64656), \operatorname{Matrix}.\operatorname{vecCons}\left(43848, \operatorname{Matrix}.\operatorname{vecCons}\left(214008, \operatorname{Matrix}.\operatorname{vecCons}\left((-371692), \operatorname{Matrix}.\operatorname{vecCons}\left((-48036), \operatorname{Matrix}.\operatorname{vecCons}\left(498819, \operatorname{Matrix}.\operatorname{vecCons}\left((-211910), \operatorname{Matrix}.\operatorname{vecCons}\left((-256127), \operatorname{Matrix}.\operatorname{vecCons}\left(183692, \operatorname{Matrix}.\operatorname{vecCons}\left(55115, \operatorname{Matrix}.\operatorname{vecCons}\left((-59620), \operatorname{Matrix}.\operatorname{vecCons}\left((-4121), \operatorname{Matrix}.\operatorname{vecCons}\left(8804, \operatorname{Matrix}.\operatorname{vecCons}\left((-123), \operatorname{Matrix}.\operatorname{vecCons}\left((-566), \operatorname{Matrix}.\operatorname{vecCons}\left(26, \operatorname{Matrix}.\operatorname{vecCons}\left(12, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.coefficients538` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The entries are ordered from the smallest shift of the recurrence to the largest.

**Theorem 1.27 (vector_polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{22}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(20\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229538Strip}.\operatorname{coefficients538}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{(2) + (\operatorname{Fin}.\operatorname{val}\left(k\right))}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.vector_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The relation holds simultaneously for all boundary columns and both residual budgets.

**Theorem 1.28 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (23)\right): \operatorname{Int}) = ((((((((((((((((((((12) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (22)\right): \operatorname{Int}))) + ((26) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (21)\right): \operatorname{Int})))) - ((566) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (20)\right): \operatorname{Int})))) - ((123) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (19)\right): \operatorname{Int})))) + ((8804) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (18)\right): \operatorname{Int})))) - ((4121) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (17)\right): \operatorname{Int})))) - ((59620) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (16)\right): \operatorname{Int})))) + ((55115) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int})))) + ((183692) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int})))) - ((256127) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) - ((211910) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) + ((498819) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) - ((48036) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) - ((371692) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) + ((214008) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) + ((43848) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) - ((64656) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((8640) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((5184) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((1296) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The transfer counts labelled arrays by adjacent column cuts. The six-to-one count in labelled_scale identifies that readout with six times a at the widths of the recurrence. Cancelling six in the integer readout gives the order-twenty recurrence for every width at least twenty-three.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.bondDefects_empty`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.canonicalCount`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.classIndex`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.coefficients538`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost_countCut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.countCut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.edges`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.labelled_scale`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.movesOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.oneDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.residual`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.step_one`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.tableOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.table_powers`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transfer_readout`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transition_entry`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.vector_polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weight_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weights`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zeroValues`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_cost_entry`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_values`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
