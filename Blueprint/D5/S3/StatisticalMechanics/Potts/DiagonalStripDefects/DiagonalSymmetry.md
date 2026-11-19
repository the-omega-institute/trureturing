# Diagonal strip transfer

## Abstract

Exact diagonal-strip transfer identities.

**Theorem 1.1 (lift_counts).**

$$\forall d: \mathit{Nat}, (\forall t: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right), \mathit{Int}\right), ((\forall i: \operatorname{\mathit{Fin}}\left(8\right), (\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{representatives}}\left(i\right), r\right) = d) \land (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = t\left(i, j\right)))) \implies (\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}, p, r\right) = d) \land (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(r\right) = j)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0): \mathit{Int})) = t\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right), j\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry.lift_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The hypothesis fixes the successor count at each representative. Independent permutations on odd and even column indices, with reflection when needed, preserve the inter-row equality count and give a bijection on successor rows. Thus the same matrix counts every labelled source row.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry.lift_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
