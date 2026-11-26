# Two-defect HA strips

## Abstract

Exact two-defect six-column sheared square-lattice counts.

**Theorem 1.1 (forward_certificate).**

$$((\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((0: \operatorname{\mathit{Fin}}\left(12\right))\right) = \operatorname{\mathit{HardinA229692StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(11\right), (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((11: \operatorname{\mathit{Fin}}\left(12\right))\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(9\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((\begin{pmatrix}531441&(-1771470)&2460375&(-1842183)&803115&(-205200)&29368&(-2145)&75\end{pmatrix}\left(j\right): \mathit{Int}), \operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(12\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripForward.forward_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

The cached vectors and the polynomial identity propagate the registered recurrence to every later strip length.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripForward.forward_certificate`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate](../StripDefects/HardinA229584StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripData](HardinA229692StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited](HardinA229692StripInherited.md)
