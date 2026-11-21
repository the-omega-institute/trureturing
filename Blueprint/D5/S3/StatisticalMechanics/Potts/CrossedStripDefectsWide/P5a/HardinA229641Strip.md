# Canonical two-defect colourings of five-row HDA arrays

## Abstract

Canonical two-defect colourings of five-row HDA arrays

Colours are introduced in row-major order. At the widths used in the recurrence, each canonical array has six distinct label permutations.

**Definition 1.1 (a).**

$$\forall (n: \operatorname{Nat}), (\operatorname{HardinA229641Strip}.\operatorname{a}\left(n\right) = \operatorname{HardinA229538Strip}.\operatorname{canonicalCount}\left(2, n\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The filter counts all literal five-by-n arrays with exactly two monochromatic horizontal, diagonal or antidiagonal bonds and canonical colour introduction.

**Theorem 1.2 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (34)\right): \operatorname{Int}) = ((((((((((((((((((((((((((((((18) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (33)\right): \operatorname{Int}))) - ((15) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (32)\right): \operatorname{Int})))) - ((1191) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (31)\right): \operatorname{Int})))) + ((3468) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (30)\right): \operatorname{Int})))) + ((31983) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (29)\right): \operatorname{Int})))) - ((108707) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (28)\right): \operatorname{Int})))) - ((424479) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (27)\right): \operatorname{Int})))) + ((1614489) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (26)\right): \operatorname{Int})))) + ((2851598) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (25)\right): \operatorname{Int})))) - ((13478352) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (24)\right): \operatorname{Int})))) - ((7797810) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (23)\right): \operatorname{Int})))) + ((66347438) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (22)\right): \operatorname{Int})))) - ((12632640) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (21)\right): \operatorname{Int})))) - ((190067859) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (20)\right): \operatorname{Int})))) + ((147888798) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (19)\right): \operatorname{Int})))) + ((287096430) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (18)\right): \operatorname{Int})))) - ((412178619) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (17)\right): \operatorname{Int})))) - ((138135927) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (16)\right): \operatorname{Int})))) + ((522690894) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int})))) - ((168525432) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int})))) - ((273411640) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) + ((227616084) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) + ((9610272) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) - ((73617984) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) + ((21460464) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) + ((7359984) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) - ((4611168) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) + ((186624) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((279936) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) - ((46656) \cdot ((\operatorname{HardinA229641Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229641` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229641","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The order-thirty recurrence holds for every width at least thirty-four. Each natural count is cast to the integers before coefficients are applied.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Recurrence.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip](HardinA229538Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData](HardinA229538StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate](HardinA229641StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
