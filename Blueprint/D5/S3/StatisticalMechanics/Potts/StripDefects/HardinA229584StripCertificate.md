# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

A monochromatic bond is one unsatisfied bond of the three-state Potts antiferromagnet. Horizontal and antidiagonal bonds form a sheared square-lattice strip. Exactly one such bond is allowed. All equalities here concern finite combinatorial counts.

**Theorem 1.1 (tail_bound).**

$$\forall r: \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Row}}, (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate.tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

For every row r, the number of equal adjacent pairs in the five-site boundary of r is at most the number of monochromatic horizontal bonds of r. For a constant row the two counts are 4 and 5, so the inequality can be strict.

**Theorem 1.2 (Structural and forward-table certificate).**

$$(\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \mathit{Row}, ((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall r: \mathit{Row}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(32\right), (\sum_{r: \mathit{Row}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229584StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(7\right), (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229584StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(7\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-6561), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(14580, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-12150), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4662, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-805), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(50, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229584StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate.structural_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229584: one-defect three-colour width-6 sheared strips*. URL: <https://oeis.org/A229584>.

*Commentary.*

All initial, terminal, budget and forward-table identities are checked over the displayed finite domains.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate.structural_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripCertificate.tail_bound`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](HardinA229584StripData.md)
