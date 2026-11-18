# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Theorem 1.1 (structural_certificate).**

$$(\forall p: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int})))))) \land ((\forall p: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{Valid}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right))\right))))))) \land ((\forall r: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \implies (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{Valid}}\left(r, 2 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land (\forall s: \operatorname{\mathit{Fin}}\left(15\right), (\sum_{r: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \land (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(r, 2 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{initial}}\left(s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCertificate.structural_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

Acceptance, budget preservation, initial admissibility, and initial class weights for exact budget two. Natural subtraction is truncated at zero.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCertificate.structural_certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData](HardinA229696StripData.md)
