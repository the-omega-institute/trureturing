# Canonical two-defect colourings of five-row HDA arrays

## Abstract

Canonical two-defect colourings of five-row HDA arrays

Colours are introduced in row-major order. At the widths used in the recurrence, each canonical array has six distinct label permutations.

**Definition 1.1 (a).**

$$\forall (n: \operatorname{Nat}), (((\operatorname{HardinA229641Strip}.\operatorname{a}\left(n\right): \operatorname{Nat}) = \operatorname{HardinA229637RowColumn}.\operatorname{T}\left(5, n\right)) \land (\operatorname{HardinA229637RowColumn}.\operatorname{T}\left(5, n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right))\mapsto ((\operatorname{DefectTransfer}.\operatorname{defects}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (e: (\operatorname{Fin}\left(n\right))\times(\operatorname{Fin}\left(n\right)))\mapsto (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(e\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(e\right)\right)) + (1))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right))\times(\operatorname{Fin}\left(n\right))\right))\right), \operatorname{Finset}.\operatorname{filter}\left((\lambda (e: (\operatorname{Fin}\left(n\right))\times(\operatorname{Fin}\left(n\right)))\mapsto ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(e\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(e\right)\right)) + (1)) \lor (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(e\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(e\right)\right)) + (1)))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right))\times(\operatorname{Fin}\left(n\right))\right))\right), \operatorname{List}.\operatorname{ofFn}\left((\lambda (i: \operatorname{Fin}\left(5\right))\mapsto ((\lambda (j: \operatorname{Fin}\left(n\right))\mapsto (A\left((i, j)\right)))))\right)\right) = 2) \land (\forall (p: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right))), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right))), ((((n) \cdot (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right))) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((n) \cdot (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right))) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = c)))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(5\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The five-row entry of the A229637 table counts arrays with exactly two monochromatic horizontal, diagonal or antidiagonal bonds and canonical row-major colour introduction.

Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.

**Definition 1.2 (twoDefect).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229641Strip}.\operatorname{twoDefect}\left(p, q\right): \operatorname{Int}) = (\operatorname{if} (\operatorname{HardinA229538Strip}.\operatorname{cost}\left(p, q\right) = 2) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.twoDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

This entry is one exactly when a cut contains two monochromatic bonds.

**Definition 1.3 (transfer).**

$$(\operatorname{HardinA229641Strip}.\operatorname{transfer}: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)\right), \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)\right), \operatorname{Int}\right)) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233178Chromatic}.\operatorname{T}, \operatorname{Matrix}.\operatorname{fromCols}\left(\operatorname{HardinA229538Strip}.\operatorname{oneDefect}, \operatorname{HardinA229641Strip}.\operatorname{twoDefect}\right), (0: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Int}\right)), \operatorname{HardinA229538Strip}.\operatorname{transfer}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The left summand has budget two. The inherited right summand has budgets one and zero.

**Definition 1.4 (terminal).**

$$(\operatorname{HardinA229641Strip}.\operatorname{terminal}: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left((0: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), \operatorname{HardinA229538Strip}.\operatorname{terminal}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

An empty continuation requires a remaining budget of zero.

**Definition 1.5 (coefficients641).**

$$(\operatorname{HardinA229641Strip}.\operatorname{coefficients641}: \operatorname{Fin}\left(30\right) \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{vecCons}\left((-46656), \operatorname{Matrix}.\operatorname{vecCons}\left(279936, \operatorname{Matrix}.\operatorname{vecCons}\left(186624, \operatorname{Matrix}.\operatorname{vecCons}\left((-4611168), \operatorname{Matrix}.\operatorname{vecCons}\left(7359984, \operatorname{Matrix}.\operatorname{vecCons}\left(21460464, \operatorname{Matrix}.\operatorname{vecCons}\left((-73617984), \operatorname{Matrix}.\operatorname{vecCons}\left(9610272, \operatorname{Matrix}.\operatorname{vecCons}\left(227616084, \operatorname{Matrix}.\operatorname{vecCons}\left((-273411640), \operatorname{Matrix}.\operatorname{vecCons}\left((-168525432), \operatorname{Matrix}.\operatorname{vecCons}\left(522690894, \operatorname{Matrix}.\operatorname{vecCons}\left((-138135927), \operatorname{Matrix}.\operatorname{vecCons}\left((-412178619), \operatorname{Matrix}.\operatorname{vecCons}\left(287096430, \operatorname{Matrix}.\operatorname{vecCons}\left(147888798, \operatorname{Matrix}.\operatorname{vecCons}\left((-190067859), \operatorname{Matrix}.\operatorname{vecCons}\left((-12632640), \operatorname{Matrix}.\operatorname{vecCons}\left(66347438, \operatorname{Matrix}.\operatorname{vecCons}\left((-7797810), \operatorname{Matrix}.\operatorname{vecCons}\left((-13478352), \operatorname{Matrix}.\operatorname{vecCons}\left(2851598, \operatorname{Matrix}.\operatorname{vecCons}\left(1614489, \operatorname{Matrix}.\operatorname{vecCons}\left((-424479), \operatorname{Matrix}.\operatorname{vecCons}\left((-108707), \operatorname{Matrix}.\operatorname{vecCons}\left(31983, \operatorname{Matrix}.\operatorname{vecCons}\left(3468, \operatorname{Matrix}.\operatorname{vecCons}\left((-1191), \operatorname{Matrix}.\operatorname{vecCons}\left((-15), \operatorname{Matrix}.\operatorname{vecCons}\left(18, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.coefficients641` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The entries are ordered from the smallest shift of the recurrence to the largest.

**Theorem 1.6 (vector_polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229641Strip}.\operatorname{transfer})^{33}, \operatorname{HardinA229641Strip}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(30\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229641Strip}.\operatorname{coefficients641}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229641Strip}.\operatorname{transfer})^{(3) + (\operatorname{Fin}.\operatorname{val}\left(k\right))}, \operatorname{HardinA229641Strip}.\operatorname{terminal}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.vector_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The relation holds simultaneously for all boundary columns and all three residual budgets.

**Theorem 1.7 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (34)\right): \operatorname{Int}) = ((((((((((((((((((((((((((((((18) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (33)\right): \operatorname{Int}))) - ((15) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (32)\right): \operatorname{Int})))) - ((1191) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (31)\right): \operatorname{Int})))) + ((3468) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (30)\right): \operatorname{Int})))) + ((31983) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (29)\right): \operatorname{Int})))) - ((108707) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (28)\right): \operatorname{Int})))) - ((424479) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (27)\right): \operatorname{Int})))) + ((1614489) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (26)\right): \operatorname{Int})))) + ((2851598) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (25)\right): \operatorname{Int})))) - ((13478352) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (24)\right): \operatorname{Int})))) - ((7797810) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (23)\right): \operatorname{Int})))) + ((66347438) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (22)\right): \operatorname{Int})))) - ((12632640) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (21)\right): \operatorname{Int})))) - ((190067859) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (20)\right): \operatorname{Int})))) + ((147888798) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (19)\right): \operatorname{Int})))) + ((287096430) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (18)\right): \operatorname{Int})))) - ((412178619) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (17)\right): \operatorname{Int})))) - ((138135927) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (16)\right): \operatorname{Int})))) + ((522690894) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int})))) - ((168525432) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int})))) - ((273411640) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) + ((227616084) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) + ((9610272) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) - ((73617984) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) + ((21460464) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) + ((7359984) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) - ((4611168) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) + ((186624) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((279936) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) - ((46656) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229641` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229641","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

For each array, the table scans horizontal bonds within rows and diagonal and antidiagonal bonds between rows. In the transfer, each of these bonds lies in the cut of its two consecutive columns. Interchanging the finite row and column sums for each bond direction gives the same number of monochromatic bonds, and both filters impose the same row-major canonical condition. The labelled readout is therefore six times the table entry at each width used in the recurrence. Cancelling six over the integers gives the order-thirty recurrence for every width at least thirty-four.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.coefficients641`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.twoDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.vector_polynomial`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip](HardinA229538Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge](../../KingDefects/TwoDefectStrips/GridBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn](../../StripDefects/HardinA229637RowColumn.md)
