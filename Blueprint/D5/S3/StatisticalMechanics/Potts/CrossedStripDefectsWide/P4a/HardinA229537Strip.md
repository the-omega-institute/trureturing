# HardinA229537Strip

## Abstract

Four-row exact-defect HDA strips.

The filter counts every actual four-by-n array over Fin 3 with one monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least fifteen.

**Definition 1.1 (a).**

$$\forall (n: \operatorname{Nat}), (\operatorname{HardinA229537Strip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right))\mapsto ((\operatorname{DefectTransfer}.\operatorname{defects}\left(\operatorname{HardinA229537StripData}.\operatorname{horizontal}, \operatorname{HardinA229537StripData}.\operatorname{between}, \operatorname{List}.\operatorname{ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right))\mapsto ((\lambda (i: \operatorname{Fin}\left(4\right))\mapsto (A\left((i, j)\right)))))\right)\right) = 1) \land (\forall (p: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right))), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = c)))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

The filter counts every actual four-by-n array over Fin 3 with one monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least fifteen.

**Theorem 1.2 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int}) = ((((((((((((6) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int}))) + ((23) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) - ((102) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) - ((288) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) + ((250) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) + ((787) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) - ((238) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) - ((741) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) + ((124) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((196) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) - ((16) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((16) \cdot ((\operatorname{HardinA229537Strip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

The filter counts every actual four-by-n array over Fin 3 with one monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least fifteen.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate](HardinA229537StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData](HardinA229537StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripCertificate](../../StripDefects/HardinA229589StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../../StripDefects/HardinA229589StripData.md)
