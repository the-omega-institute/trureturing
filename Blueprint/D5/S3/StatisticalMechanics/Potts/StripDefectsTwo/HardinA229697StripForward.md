# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Theorem 1.1 (forward_certificate).**

$$((\operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}\left((0: \operatorname{\mathit{Fin}}\left(18\right))\right) = \operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(17\right), (\operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229697StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}\left((17: \operatorname{\mathit{Fin}}\left(18\right))\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(9\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((![216, (-1620), 5022, (-8343), 8073, (-4644), 1557, (-288), 27]\left(j\right): \mathit{Int}), \operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(8 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(18\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripForward.forward_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The first 13 leading rows reuse the frozen forward certificate. The appended rows and new sector are checked in the kernel. Scalar multiplication acts on integer vectors.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripForward.forward_certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip](../StripDefects/HardinA229589Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../StripDefects/HardinA229589StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData](HardinA229697StripData.md)
