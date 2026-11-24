# Canonical one-defect colourings of five-row HDA arrays

## Abstract

Canonical one-defect colourings of five-row HDA arrays

Colours are introduced in row-major order. At the widths used in the recurrence, the exact defect count excludes constant arrays. Each counted array has six distinct labelled representatives.

**Definition 1.1 (canonicalCount).**

$$\forall (k: \operatorname{Nat}), (\forall (H: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(k\right))\right)), (\forall (V: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(k\right))\right)), (\forall (D: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(H, V, D, n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right))\mapsto ((\operatorname{DefectTransfer}.\operatorname{defects}\left(H, V, \operatorname{List}.\operatorname{ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right))\mapsto ((\lambda (i: \operatorname{Fin}\left(k\right))\mapsto (A\left((i, j)\right)))))\right)\right) = D) \land (\forall (p: (\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(n\right))), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: (\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = c)))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.canonicalCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The filter counts arrays of height k and width n with exactly D monochromatic bonds for the cuts H and V and row-major canonical colour introduction.

**Definition 1.2 (a).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{HardinA229538Strip}.\operatorname{a}\left(n\right): \operatorname{Nat}) = \operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), \operatorname{HardinA229538Strip}.\operatorname{edges}, 1, n\right)) \land (\operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), \operatorname{HardinA229538Strip}.\operatorname{edges}, 1, n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right))\mapsto ((\operatorname{DefectTransfer}.\operatorname{defects}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)), \operatorname{Finset}.\operatorname{filter}\left((\lambda ((r, s): (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right)))\mapsto (\operatorname{Fin}.\operatorname{val}\left(s\right) = \operatorname{Fin}.\operatorname{val}\left(r\right) \lor \left(\operatorname{Fin}.\operatorname{val}\left(s\right) = (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1) \lor \operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right))\right), \operatorname{List}.\operatorname{ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right))\mapsto ((\lambda (i: \operatorname{Fin}\left(5\right))\mapsto (A\left((i, j)\right)))))\right)\right) = 1) \land (\forall (p: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right))), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = c)))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The column-sweep count uses defect budget one.

**Definition 1.3 (residual).**

$$\forall (C: \operatorname{Type}*), (\forall (p: C), (\forall (d: \operatorname{Nat}), ((\operatorname{HardinA229538Strip}.\operatorname{residual}\left(p, d\right): \operatorname{Sum}\left(C, C\right)) = (\operatorname{if} (d = 0) \operatorname{then} \operatorname{Sum}.\operatorname{inr}\left(p\right) \operatorname{else} \operatorname{Sum}.\operatorname{inl}\left(p\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Budgets zero and one select the right and left summands respectively.

**Theorem 1.4 (transition_entry).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (d: \operatorname{Nat}), (\forall (s: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)), ((((\operatorname{if} ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) \le d) \land (\operatorname{HardinA229538Strip}.\operatorname{residual}\left(q, (d) - (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right))\right) = s)) \operatorname{then} 1 \operatorname{else} 0): \operatorname{Int})) - ((\operatorname{if} (\operatorname{Sum}.\operatorname{elim}\left(\operatorname{id}, \operatorname{id}, s\right) = q) \operatorname{then} \operatorname{HardinA229538Strip}.\operatorname{transfer}\left(\operatorname{HardinA229538Strip}.\operatorname{residual}\left(p, d\right), s\right) \operatorname{else} 0)) = (\operatorname{if} ((1 < d) \land ((0 < \operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right)) \land (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) \le d))) \operatorname{then} ((\operatorname{if} (s = \operatorname{HardinA229538Strip}.\operatorname{residual}\left(q, (d) - (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right))\right)) \operatorname{then} 1 \operatorname{else} 0)) - ((\operatorname{if} ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 1) \land (s = \operatorname{Sum}.\operatorname{inr}\left(q\right))) \operatorname{then} 1 \operatorname{else} 0)) \operatorname{else} 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transition_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

For a budget above one and a positive cost within that budget, the difference of the entries is +1 at the affordable residual successor and −1 at the exhausted successor when the cost is one. The difference is zero in all other cases.

**Theorem 1.5 (labelled_scale).**

$$\forall (k: \operatorname{Nat}), (\forall (H: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(k\right))\right)), (\forall (V: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(k\right))\right)), (\forall (D: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), ((\left(\operatorname{DefectTransfer}.\operatorname{literalCount}_{3}\right)\left(H, V, D, n\right)) + ((\operatorname{if} ((k = 0) \lor (n = 0)) \operatorname{then} (\operatorname{if} (D = 0) \operatorname{then} 5 \operatorname{else} 0) \operatorname{else} (\operatorname{if} (D = (\operatorname{Finset}.\operatorname{card}\left(H\right)) + ((\operatorname{Nat}.\operatorname{pred}\left(n\right)) \cdot ((\operatorname{Finset}.\operatorname{card}\left(V\right)) + (\operatorname{Finset}.\operatorname{card}\left(H\right))))) \operatorname{then} 3 \operatorname{else} 0))) = (6) \cdot (\operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(H, V, D, n\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.labelled_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The subscript 3 on the literal count is the palette parameter q := 3. The nonconstant arrays contribute six labelled representatives per canonical array. At positive height and width, the three constant arrays contribute one canonical class at budget H.card plus (n − 1) times the sum of the cut cardinalities. At height or width zero, the unique empty array contributes one labelled and one canonical representative at budget zero. The correction is three in the former case and five in the latter.

Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.

**Definition 1.6 (edges).**

$$(\operatorname{HardinA229538Strip}.\operatorname{edges}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right))\right)) = \operatorname{Finset}.\operatorname{diag}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(5\right)\right))\right) \cup \operatorname{HardinA229637RowColumn}.\operatorname{betw}\left(5\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The oriented cut contains the pairs of rows at distance at most one across consecutive columns. It is the disjoint union of the straight pairs and the two orientations of adjacent-row pairs.

**Theorem 1.7 (cut_total_exclusion).**

$$\forall (k: \operatorname{Nat}), (\forall (D: \operatorname{Nat}), ((\forall (m: \operatorname{Nat}), (D \ne (m) \cdot (\operatorname{Finset}.\operatorname{card}\left((\operatorname{Finset}.\operatorname{diag}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))\right) \cup \operatorname{HardinA229637RowColumn}.\operatorname{betw}\left(k\right))\right)))) \Leftrightarrow (\neg ((k) + ((2) \cdot ((k) - (1))) \mid D))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cut_total_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

A budget differs from the total for every number of cuts exactly when the cut cardinality does not divide the budget. At height k there are k same-row pairs and k − 1 pairs in each diagonal direction, with subtraction in the naturals. At height five this gives thirteen pairs.

**Definition 1.8 (cost).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right): \operatorname{Nat}) = \operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229538Strip}.\operatorname{edges}, \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(q\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The cost is the number of monochromatic bonds on the cut between two decoded columns.

**Theorem 1.9 (bondDefects_empty).**

$$\forall (q: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (r: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(q\right)), (\forall (t: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(q\right)), (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left((\operatorname{Finset}.\operatorname{empty}: \operatorname{Finset}\left((\operatorname{Fin}\left(k\right))\times(\operatorname{Fin}\left(k\right))\right)), r, t\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.bondDefects_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

For any pair of rows, the empty edge set contributes zero monochromatic bonds.

**Theorem 1.10 (cost_zero).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 0) \Leftrightarrow (\operatorname{HardinA233178Chromatic}.\operatorname{Bond}\left(p, q\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

A cut has cost zero exactly when every bond has different colours at its endpoints.

**Theorem 1.11 (zero_cost_entry).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{if} (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 0) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} 0) = \operatorname{HardinA233178Chromatic}.\operatorname{T}\left(p, q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_cost_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The proper-colouring transfer entry is the indicator of a cut without monochromatic bonds.

**Definition 1.12 (oneDefect).**

$$\forall (R: \operatorname{Type}*), ([\operatorname{Zero}\left(R\right)] [\operatorname{One}\left(R\right)] \forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{oneDefect}\left(p, q\right): R) = (\operatorname{if} (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 1) \operatorname{then} 1 \operatorname{else} 0))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.oneDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Each entry is the indicator of a cut with exactly one monochromatic bond.

**Definition 1.13 (transfer).**

$$(\operatorname{HardinA229538Strip}.\operatorname{transfer}: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{Int}\right)) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233178Chromatic}.\operatorname{T}, \operatorname{HardinA229538Strip}.\operatorname{oneDefect}, (0: \operatorname{Matrix}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Int}\right)), \operatorname{HardinA233178Chromatic}.\operatorname{T}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The two summands represent one and zero residual defects. A zero-cost cut preserves the budget and a cut of cost one moves from the first summand to the second.

**Definition 1.14 (terminal).**

$$\forall (C: \operatorname{Type}*), (\forall (Z: \operatorname{Type}*), (\forall (R: \operatorname{Type}*), ([\operatorname{Zero}\left(R\right)] [\operatorname{One}\left(R\right)] (\operatorname{HardinA229538Strip}.\operatorname{terminal}: \operatorname{Sum}\left(C, Z\right) \to R) = \operatorname{Sum}.\operatorname{elim}\left((0: C \to R), (1: Z \to R)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The empty continuation completes an array exactly when its remaining budget is zero.

**Theorem 1.15 (edges_sum).**

$$\forall (M: \operatorname{Type}*), ([\operatorname{AddCommMonoid}\left(M\right)] \forall (f: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(5\right)) \to M), (\operatorname{Finset}.\operatorname{sum}\left(\operatorname{HardinA229538Strip}.\operatorname{edges}, f\right) = ((((((((((((f\left((0, 0)\right)) + (f\left((0, 1)\right))) + (f\left((1, 0)\right))) + (f\left((1, 1)\right))) + (f\left((1, 2)\right))) + (f\left((2, 1)\right))) + (f\left((2, 2)\right))) + (f\left((2, 3)\right))) + (f\left((3, 2)\right))) + (f\left((3, 3)\right))) + (f\left((3, 4)\right))) + (f\left((4, 3)\right))) + (f\left((4, 4)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.edges_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

For any additive commutative monoid, summing the edge weights over the cut gives the thirteen displayed terms. Both defect certificates assign weight one when the two endpoint colours agree and zero otherwise.

**Definition 1.16 (movesOne).**

$$(\operatorname{HardinA229538Strip}.\operatorname{movesOne}: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{List}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.movesOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The Lean definition is the literal vector of 243 successor lists. Applying the vector to a column code selects its list. Each stored list contains the eligible columns in code order.

**Theorem 1.17 (step_one).**

$$\forall (R: \operatorname{Type}*), ([\operatorname{AddCommMonoid}\left(R\right)] [\operatorname{Mul}\left(R\right)] [\operatorname{One}\left(R\right)] \forall (w: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to R), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column})\mapsto ((\neg (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 1)))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}\right))\right), (\lambda (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column})\mapsto (((0: R)) \cdot (w\left(q\right))))\right) = (0: R)) \Rightarrow (\operatorname{dotProduct}\left(\operatorname{HardinA229538Strip}.\operatorname{oneDefect}\left(p\right), w\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\lambda (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column})\mapsto (((1: R)) \cdot (w\left(q\right)))), \operatorname{HardinA229538Strip}.\operatorname{movesOne}\left(p\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.step_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The list enumerates without duplicates the successor columns whose cut from p has cost one. The indicator dot product equals its weighted sum when the sum over the omitted columns is zero.

**Definition 1.18 (weights).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538Strip}.\operatorname{weights}\left(n\right) = (\operatorname{if} ((h: \operatorname{Fin}.\operatorname{val}\left(n\right) < 12)) \operatorname{then} (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(12\right), \operatorname{Fin}\left(12\right), \operatorname{Int}\right))\left(\operatorname{Fin}.\operatorname{castLT}\left(n, h\right)\right) \operatorname{else} (\operatorname{if} ((hn: \operatorname{Fin}.\operatorname{val}\left(n\right) = 12)) \operatorname{then} \operatorname{Fin}.\operatorname{append}\left((0: \operatorname{Fin}\left(2\right) \to \operatorname{Int}), \operatorname{HardinA233178Chromatic}.\operatorname{coefficients}\right) \operatorname{else} (\operatorname{let} (later: \operatorname{Fin}\left(10\right) \to \left(\operatorname{Fin}\left(12\right) \to \mathbb{Z}\right)) := \text{stored Lean literal} \operatorname{in} (later\left(\operatorname{Fin}.\operatorname{subNat}\left(13, n, \operatorname{Nat}.\operatorname{lt_{of_{le_{of_{ne}}}}}\left(\operatorname{Nat}.\operatorname{le_{of_{not_{gt}}}}\left(h\right), \operatorname{Ne}.\operatorname{symm}\left(hn\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The first twelve rows come from the identity matrix. The row at exponent twelve appends the proper-colouring coefficients to two zeros. For exponents thirteen through twenty-two, the local literal later in the Lean definition supplies row n minus thirteen.

**Definition 1.19 (classIndex).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{classIndex}\left(p\right): \operatorname{Fin}\left(25\right)) = (\operatorname{Matrix}.\operatorname{vecCons}\left(0, \operatorname{Matrix}.\operatorname{vecCons}\left(1, \operatorname{Matrix}.\operatorname{vecCons}\left(2, \operatorname{Matrix}.\operatorname{vecCons}\left(3, \operatorname{Matrix}.\operatorname{vecCons}\left(4, \operatorname{Matrix}.\operatorname{vecCons}\left(5, \operatorname{Matrix}.\operatorname{vecCons}\left(6, \operatorname{Matrix}.\operatorname{vecCons}\left(7, \operatorname{Matrix}.\operatorname{vecCons}\left(8, \operatorname{Matrix}.\operatorname{vecCons}\left(3, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecCons}\left(10, \operatorname{Matrix}.\operatorname{vecCons}\left(11, \operatorname{Matrix}.\operatorname{vecCons}\left(12, \operatorname{Matrix}.\operatorname{vecCons}\left(2, \operatorname{Matrix}.\operatorname{vecCons}\left(13, \operatorname{Matrix}.\operatorname{vecCons}\left(14, \operatorname{Matrix}.\operatorname{vecCons}\left(15, \operatorname{Matrix}.\operatorname{vecCons}\left(6, \operatorname{Matrix}.\operatorname{vecCons}\left(16, \operatorname{Matrix}.\operatorname{vecCons}\left(17, \operatorname{Matrix}.\operatorname{vecCons}\left(18, \operatorname{Matrix}.\operatorname{vecCons}\left(11, \operatorname{Matrix}.\operatorname{vecCons}\left(8, \operatorname{Matrix}.\operatorname{vecCons}\left(13, \operatorname{Matrix}.\operatorname{vecCons}\left(19, \operatorname{Matrix}.\operatorname{vecCons}\left(20, \operatorname{Matrix}.\operatorname{vecCons}\left(1, \operatorname{Matrix}.\operatorname{vecCons}\left(21, \operatorname{Matrix}.\operatorname{vecCons}\left(22, \operatorname{Matrix}.\operatorname{vecCons}\left(14, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecCons}\left(10, \operatorname{Matrix}.\operatorname{vecCons}\left(23, \operatorname{Matrix}.\operatorname{vecCons}\left(18, \operatorname{Matrix}.\operatorname{vecCons}\left(24, \operatorname{Matrix}.\operatorname{vecCons}\left(7, \operatorname{Matrix}.\operatorname{vecCons}\left(16, \operatorname{Matrix}.\operatorname{vecCons}\left(22, \operatorname{Matrix}.\operatorname{vecCons}\left(19, \operatorname{Matrix}.\operatorname{vecCons}\left(4, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right): \operatorname{Fin}\left(41\right) \to \operatorname{Fin}\left(25\right))\left(\operatorname{HardinA233260Literal}.\operatorname{cls}\left((\operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(0\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(1\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(2\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(3\right), \operatorname{HardinA233178Recurrence}.\operatorname{columnEquiv}\left(p\right)\left(4\right))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.classIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The lookup classifies five-entry boundary columns under colour permutation and row reversal.

**Definition 1.20 (tableOne).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{tableOne}\left(n, p\right): \operatorname{Int}) = (\operatorname{let} (values: \operatorname{Fin}\left(23\right) \to \left(\operatorname{Fin}\left(25\right) \to \mathbb{Z}\right)) := \text{stored Lean literal} \operatorname{in} (values\left(n, \operatorname{HardinA229538Strip}.\operatorname{classIndex}\left(p\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.tableOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The local literal values in the Lean definition has 23 rows and 25 columns. The indices are the exponent n and the class of p. The theorem table_powers pins this lookup through the first summand of the continuation vector.

**Definition 1.21 (zeroValues).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229538Strip}.\operatorname{zeroValues}\left(n, p\right): \operatorname{Int}) = (\operatorname{if} ((h: \operatorname{Fin}.\operatorname{val}\left(n\right) < 12)) \operatorname{then} \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(\operatorname{Fin}.\operatorname{castLT}\left(n, h\right), p\right) \operatorname{else} \sum_{(j: \operatorname{Fin}\left(12\right))} ((\operatorname{HardinA229538Strip}.\operatorname{weights}\left(n, j\right)) \cdot (\operatorname{HardinA233178Chromatic}.\operatorname{table}\left(j, p\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zeroValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

For larger exponents the zero-defect values are linear combinations of the twelve proper-colouring vectors.

**Theorem 1.22 (weight_eq).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538Strip}.\operatorname{zeroValues}\left(n\right) = \sum_{(j: \operatorname{Fin}\left(12\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229538Strip}.\operatorname{weights}\left(n, j\right), \operatorname{HardinA233178Chromatic}.\operatorname{table}\left(j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weight_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The same coefficient formula also holds at the tabulated exponents.

**Theorem 1.23 (zero_values).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{HardinA229538Strip}.\operatorname{zeroValues}\left(n\right) = \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The reconstructed value is the proper-colouring continuation vector at each exponent.

**Theorem 1.24 (table_powers).**

$$\forall (n: \operatorname{Fin}\left(23\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{HardinA229538Strip}.\operatorname{tableOne}\left(n\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA233178Chromatic}.\operatorname{T})^{\operatorname{Fin}.\operatorname{val}\left(n\right)}, (1: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.table_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The first coordinate gives the one-defect continuations and the second gives the inherited proper-colouring continuations.

**Definition 1.25 (coefficients538).**

$$(\operatorname{HardinA229538Strip}.\operatorname{coefficients538}: \operatorname{Fin}\left(20\right) \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{vecCons}\left((-1296), \operatorname{Matrix}.\operatorname{vecCons}\left(5184, \operatorname{Matrix}.\operatorname{vecCons}\left(8640, \operatorname{Matrix}.\operatorname{vecCons}\left((-64656), \operatorname{Matrix}.\operatorname{vecCons}\left(43848, \operatorname{Matrix}.\operatorname{vecCons}\left(214008, \operatorname{Matrix}.\operatorname{vecCons}\left((-371692), \operatorname{Matrix}.\operatorname{vecCons}\left((-48036), \operatorname{Matrix}.\operatorname{vecCons}\left(498819, \operatorname{Matrix}.\operatorname{vecCons}\left((-211910), \operatorname{Matrix}.\operatorname{vecCons}\left((-256127), \operatorname{Matrix}.\operatorname{vecCons}\left(183692, \operatorname{Matrix}.\operatorname{vecCons}\left(55115, \operatorname{Matrix}.\operatorname{vecCons}\left((-59620), \operatorname{Matrix}.\operatorname{vecCons}\left((-4121), \operatorname{Matrix}.\operatorname{vecCons}\left(8804, \operatorname{Matrix}.\operatorname{vecCons}\left((-123), \operatorname{Matrix}.\operatorname{vecCons}\left((-566), \operatorname{Matrix}.\operatorname{vecCons}\left(26, \operatorname{Matrix}.\operatorname{vecCons}\left(12, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.coefficients538` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The entries are ordered from the smallest shift of the recurrence to the largest.

**Theorem 1.26 (vector_polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{22}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(20\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229538Strip}.\operatorname{coefficients538}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229538Strip}.\operatorname{transfer})^{(2) + (\operatorname{Fin}.\operatorname{val}\left(k\right))}, \operatorname{HardinA229538Strip}.\operatorname{terminal}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.vector_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The relation holds simultaneously for all boundary columns and both residual budgets.

**Theorem 1.27 (result).**

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
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cost_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.cut_total_exclusion`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.edges`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.edges_sum`
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
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transition_entry`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.vector_polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weight_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.weights`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zeroValues`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_cost_entry`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.zero_values`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../../StripDefects/HardinA229637RowColumn.md)
