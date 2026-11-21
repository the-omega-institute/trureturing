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

$$\forall (n: \operatorname{Nat}), (\operatorname{HardinA229538Strip}.\operatorname{a}\left(n\right) = \operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(1, n\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The defect budget is one.

**Definition 1.3 (residual).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (d: \operatorname{Nat}), ((\operatorname{HardinA229538Strip}.\operatorname{residual}\left(p, d\right): \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)) = (\operatorname{if} (d = 0) \operatorname{then} \operatorname{Sum}.\operatorname{inr}\left(p\right) \operatorname{else} \operatorname{Sum}.\operatorname{inl}\left(p\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

Budgets zero and one select the right and left summands respectively.

**Theorem 1.4 (transition_entry).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (d: \operatorname{Nat}), ((d \le 1) \Rightarrow (\forall (s: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)), (((\operatorname{if} ((\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right) \le d) \land (\operatorname{HardinA229538Strip}.\operatorname{residual}\left(q, (d) - (\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right))\right) = s)) \operatorname{then} 1 \operatorname{else} 0): \operatorname{Int}) = (\operatorname{if} (\operatorname{Sum}.\operatorname{elim}\left(\operatorname{id}, \operatorname{id}, s\right) = q) \operatorname{then} \operatorname{HardinA229538StripData}.\operatorname{transfer}\left(\operatorname{HardinA229538Strip}.\operatorname{residual}\left(p, d\right), s\right) \operatorname{else} 0))))))$$

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

**Theorem 1.6 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (23)\right): \operatorname{Int}) = ((((((((((((((((((((12) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (22)\right): \operatorname{Int}))) + ((26) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (21)\right): \operatorname{Int})))) - ((566) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (20)\right): \operatorname{Int})))) - ((123) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (19)\right): \operatorname{Int})))) + ((8804) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (18)\right): \operatorname{Int})))) - ((4121) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (17)\right): \operatorname{Int})))) - ((59620) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (16)\right): \operatorname{Int})))) + ((55115) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int})))) + ((183692) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int})))) - ((256127) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) - ((211910) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) + ((498819) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) - ((48036) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) - ((371692) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) + ((214008) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) + ((43848) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) - ((64656) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((8640) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((5184) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((1296) \cdot ((\operatorname{HardinA229538Strip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229538: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229538>.

*Commentary.*

The order-twenty recurrence holds for every width at least twenty-three. Each natural count is cast to the integers before coefficients are applied.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.canonicalCount`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.labelled_scale`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.residual`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.transition_entry`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate](HardinA229538StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData](HardinA229538StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
