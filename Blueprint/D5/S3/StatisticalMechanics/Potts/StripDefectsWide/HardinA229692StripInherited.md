# Two-defect HA strips

## Abstract

Exact two-defect six-column sheared square-lattice counts.

**Theorem 1.1 (step).**

$$\forall i: \operatorname{\mathit{Fin}}\left(11\right), ((\forall j: \operatorname{\mathit{Fin}}\left(36\right), ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 7) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 11) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 16) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 20) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 26) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 29) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 30) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 31) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 34) \lor (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 35))))))))))) \implies (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right)\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(32, j\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\right)\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(32, j\right)\right)))) \implies (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229692StripData}}.\operatorname{T}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited.step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

The lower-left block is zero. HardinA229584Strip.powers_table supplies the leading prefix; its forward evolution supplies the remaining leading coordinates. Ten identical matrix columns copy those steps; only the other twenty-six coordinates require a numerical premise.

**Theorem 1.2 (polynomial).**

$$(\forall j: \operatorname{\mathit{Fin}}\left(36\right), ((\neg((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 7) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 11) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 16) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 20) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 26) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 29) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 30) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 31) \lor ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 34) \lor (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) = 35))))))))))) \implies (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((11: \operatorname{\mathit{Fin}}\left(12\right)), \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(32, j\right)\right) = \sum_{k: \operatorname{\mathit{Fin}}\left(9\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((\begin{pmatrix}531441&(-1771470)&2460375&(-1842183)&803115&(-205200)&29368&(-2145)&75\end{pmatrix}\left(k\right): \mathit{Int}), \operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right)\right): \operatorname{\mathit{Fin}}\left(12\right))\right)\right))\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(32, j\right)\right)))) \implies (\operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((11: \operatorname{\mathit{Fin}}\left(12\right))\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(9\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((\begin{pmatrix}531441&(-1771470)&2460375&(-1842183)&803115&(-205200)&29368&(-2145)&75\end{pmatrix}\left(j\right): \mathit{Int}), \operatorname{\mathit{HardinA229692StripData}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(12\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited.polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229692: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229692>.

*Commentary.*

Advance HardinA229584Strip.polynomial_relation and multiply its monic polynomial by X cubed minus twenty-five X squared plus ninety X minus eighty-one. Linearity supplies the inherited relation; only twenty-six new coordinates require a numerical premise.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited.polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited.step`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip](../StripDefects/HardinA229584Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripData](HardinA229692StripData.md)
