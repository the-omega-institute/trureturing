# HardinA229640Strip

## Abstract

Four-row exact-defect HDA strips.

The filter counts every actual four-by-n array over Fin 3 with two monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least twenty-two.

**Definition 1.1 (a).**

$$\forall (n: \operatorname{Nat}), (\operatorname{HardinA229640Strip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right))\mapsto ((\operatorname{DefectTransfer}.\operatorname{defects}\left(\operatorname{HardinA229537StripData}.\operatorname{horizontal}, \operatorname{HardinA229537StripData}.\operatorname{between}, \operatorname{List}.\operatorname{ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right))\mapsto ((\lambda (i: \operatorname{Fin}\left(4\right))\mapsto (A\left((i, j)\right)))))\right)\right) = 2) \land (\forall (p: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right))), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: (\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = c)))))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(4\right))\times(\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)\right))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The filter counts every actual four-by-n array over Fin 3 with two monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least twenty-two.

**Theorem 1.2 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (22)\right): \operatorname{Int}) = ((((((((((((((((((9) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (21)\right): \operatorname{Int}))) + ((21) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (20)\right): \operatorname{Int})))) - ((270) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (19)\right): \operatorname{Int})))) - ((357) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (18)\right): \operatorname{Int})))) + ((2967) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (17)\right): \operatorname{Int})))) + ((4906) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (16)\right): \operatorname{Int})))) - ((10083) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int})))) - ((18957) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int})))) + ((15750) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) + ((31293) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) - ((13335) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) - ((23929) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) + ((6426) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) + ((7824) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) - ((1336) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) - ((1152) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((96) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((64) \cdot ((\operatorname{HardinA229640Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229640` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229640","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The filter counts every actual four-by-n array over Fin 3 with two monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least twenty-two.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData](HardinA229537StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate](HardinA229640StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData](HardinA229640StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../../StripDefects/HardinA229589StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripCertificate](../../StripDefectsTwo/HardinA229697StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData](../../StripDefectsTwo/HardinA229697StripData.md)
