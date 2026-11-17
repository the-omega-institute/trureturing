# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Theorem 1.1 (forward_certificate).**

$$((\operatorname{\mathit{HardinA229696StripData}}.\operatorname{W}\left((0: \operatorname{\mathit{Fin}}\left(11\right))\right) = \operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(10\right), (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229696StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{W}\left((10: \operatorname{\mathit{Fin}}\left(11\right))\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((![(-8), 60, (-162), 185, (-81), 15]\left(j\right): \mathit{Int}), \operatorname{\mathit{HardinA229696StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(11\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripForward.forward_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

The first 7 leading rows reuse the frozen forward certificate. The appended rows and new sector are checked in the kernel. Scalar multiplication acts on integer vectors.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripForward.forward_certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData](HardinA229696StripData.md)
