# HardinA229537StripData

## Abstract

Four-row exact-defect HDA strips.

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

**Definition 1.1 (horizontal).**

$$\operatorname{HardinA229537StripData}.\operatorname{horizontal} = \operatorname{HardinA229589StripData}.\operatorname{horizontal}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

**Definition 1.2 (between).**

$$\operatorname{HardinA229537StripData}.\operatorname{between} = \operatorname{Finset}.\operatorname{filter}\left((\lambda (e: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(4\right)))\mapsto ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(e\right)\right) \le (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(e\right)\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(e\right)\right) \le (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(e\right)\right)) + (1)))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(4\right))\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

**Definition 1.3 (cl).**

$$\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (d: \operatorname{Nat}), (\operatorname{HardinA229537StripData}.\operatorname{cl}\left(p, d\right) = \operatorname{HardinA229589StripData}.\operatorname{cl}\left(p, (\operatorname{if} (d = 0) \operatorname{then} 0 \operatorname{else} 1)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

**Definition 1.4 (T).**

$$\operatorname{HardinA229537StripData}.\operatorname{T} = \operatorname{Matrix}.\operatorname{reindex}\left((\operatorname{finSumFinEquiv}: \operatorname{Equiv}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(14\right)\right), \operatorname{Fin}\left(28\right)\right)), (\operatorname{finSumFinEquiv}: \operatorname{Equiv}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(14\right)\right), \operatorname{Fin}\left(28\right)\right)), \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233177PairTransfer}.\operatorname{Q}, (\begin{pmatrix}0&0&0&0&0&0&0&0&0&0&0&0&0&0\\0&3&2&0&1&0&2&1&2&0&1&0&0&0\\0&2&1&1&0&1&1&0&1&0&1&0&0&0\\0&0&1&2&1&1&0&1&0&0&0&0&1&1\\0&1&0&1&1&0&0&1&0&0&1&0&0&1\\0&0&1&1&0&1&1&0&1&2&1&0&0&0\\0&2&1&0&0&1&0&0&0&2&0&0&0&0\\0&1&0&1&1&0&0&0&0&0&0&0&0&0\\0&2&1&0&0&1&0&0&0&2&0&0&0&0\\0&0&0&0&0&2&2&0&2&3&1&0&1&1\\0&1&1&0&1&1&0&0&0&1&0&0&0&1\\0&0&0&0&0&0&0&0&0&0&0&0&0&0\\0&0&0&1&0&0&0&0&0&1&0&0&0&1\\0&0&0&1&1&0&0&0&0&1&1&0&1&1\end{pmatrix}: \operatorname{Matrix}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(14\right), \operatorname{Int}\right)), (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(14\right), \operatorname{Int}\right)), \operatorname{HardinA233177PairTransfer}.\operatorname{Q}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

**Definition 1.5 (initial).**

$$\operatorname{HardinA229537StripData}.\operatorname{initial} = \operatorname{HardinA229589StripData}.\operatorname{initial}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

**Definition 1.6 (terminal).**

$$\operatorname{HardinA229537StripData}.\operatorname{terminal} = \operatorname{HardinA229589StripData}.\operatorname{terminal}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Each boundary has four colours. The classifier uses the A229589 colour classes, sending zero budget to zero and every positive budget to one. The endpoint vectors are those of A229589. The first fourteen coordinates have one remaining defect and the last fourteen have none. The diagonal blocks are the proper-colouring matrix Q. The upper block counts precisely one monochromatic bond. The original horizontal and two diagonal bonds all join successive columns; the column itself has no bonds. Fin.castAdd preserves the original index; Fin.natAdd adds the indicated offset. Fin.append concatenates finite vectors. Matrix.reindex identifies the sum of the index sets with consecutive finite indices.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../../StripDefects/HardinA229589StripData.md)
