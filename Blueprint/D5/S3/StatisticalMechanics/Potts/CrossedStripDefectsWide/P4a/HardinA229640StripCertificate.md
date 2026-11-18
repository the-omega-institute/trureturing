# HardinA229640StripCertificate

## Abstract

Four-row two-defect HDA strips.

The one-defect successor counts and continuation powers retain their original values. Exactly two monochromatic bonds define the additional transition entries. The full continuation vector satisfies the cube of the proper-colouring sextic after three transitions. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.1 (finite_certificate).**

$$(\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (d: \operatorname{Fin}\left(3\right)), (\forall (s: \operatorname{Fin}\left(42\right)), (\sum_{(r: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, p, r\right) \le \operatorname{Fin}.\operatorname{val}\left(d\right)) \land (\operatorname{HardinA229640StripData}.\operatorname{cl}\left(r, (\operatorname{Fin}.\operatorname{val}\left(d\right)) - (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, p, r\right))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229640StripData}.\operatorname{T}\left(\operatorname{HardinA229640StripData}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right), s\right))))) \land (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{HardinA229640StripData}.\operatorname{T}, 21\right), \operatorname{HardinA229640StripData}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(18\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left((\begin{pmatrix}64&96&(-1152)&(-1336)&7824&6426&(-23929)&(-13335)&31293&15750&(-18957)&(-10083)&4906&2967&(-357)&(-270)&21&9\end{pmatrix}: \operatorname{Fin}\left(18\right) \to \operatorname{Int})\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{HardinA229640StripData}.\operatorname{T}, (3) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right), \operatorname{HardinA229640StripData}.\operatorname{terminal}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The one-defect successor counts and continuation powers retain their original values. Exactly two monochromatic bonds define the additional transition entries. The full continuation vector satisfies the cube of the proper-colouring sextic after three transitions. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate.finite_certificate`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate](HardinA229537StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData](HardinA229537StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData](HardinA229640StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../../StripDefects/HardinA229589StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData](../../StripDefectsTwo/HardinA229697StripData.md)
