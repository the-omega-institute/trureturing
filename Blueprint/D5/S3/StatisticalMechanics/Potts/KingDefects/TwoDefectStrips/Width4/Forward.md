# Two-defect king transfers

## Abstract

The finite data support the literal width-4 king-grid recurrence.

The initial and terminal certificates establish the domain interpretation of the table. The Krylov identities normalize the resulting integer entries; the combined certificate retains the domain content.

**Theorem 1.1 (Acceptance, initialization and the forward relation).**

$$(\forall (p: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary}), (\forall (d: \operatorname{Fin}\left(3\right)), ((\operatorname{Data}.\operatorname{Valid}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)) \Rightarrow (\operatorname{Data}.\operatorname{terminal}\left(\operatorname{Data}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)\right) = (\operatorname{if} \operatorname{Fin}.\operatorname{val}\left(d\right) = 0 \operatorname{then} 1 \operatorname{else} 0))))) \land ((\forall (s: \operatorname{Fin}\left(19\right)), (\sum_{(r: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary})} ((\operatorname{if} (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right) \le 2) \land (\operatorname{Data}.\operatorname{cl}\left(r, (2) - (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right))\right) = s) \operatorname{then} 1 \operatorname{else} 0)) = \operatorname{Data}.\operatorname{initial}\left(s\right))) \land (((\operatorname{Data}.\operatorname{W}\left(0\right) = \operatorname{Data}.\operatorname{initial}) \land (\forall (i: \operatorname{Fin}\left(11\right)), (\operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) = \operatorname{Matrix}.\operatorname{vecMul}\left(\operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{Data}.\operatorname{T}\right)))) \land (\operatorname{Data}.\operatorname{W}\left(11\right) = \sum_{(j: \operatorname{Fin}\left(6\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Matrix}.\operatorname{vecCons}\left(-8, \operatorname{Matrix}.\operatorname{vecCons}\left(36, \operatorname{Matrix}.\operatorname{vecCons}\left(-66, \operatorname{Matrix}.\operatorname{vecCons}\left(63, \operatorname{Matrix}.\operatorname{vecCons}\left(-33, \operatorname{Matrix}.\operatorname{vecCons}\left(9, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{Data}.\operatorname{W}\left(\operatorname{Fin}.\operatorname{mk}\left((5) + (\operatorname{Fin}.\operatorname{val}\left(j\right))\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Forward.structural_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

For every valid row and budget, the terminal entry is the zero-budget indicator. The initial vector counts first rows. W(0)=initial and W(i+1)=W(i)T for i=0,...,10. Finally W(11)=-8W(5)+36W(6)-66W(7)+63W(8)-33W(9)+9W(10). Every identity is kernel checked.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Forward.structural_certificate`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data](Data.md)
