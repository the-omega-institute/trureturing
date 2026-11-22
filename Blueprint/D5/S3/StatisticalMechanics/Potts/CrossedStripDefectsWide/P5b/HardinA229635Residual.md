# Signed transfer residual

## Abstract

A scalar readout transports the signed residual through the transfer.

**Definition 1.1 (The signed lag vector).**

$$\operatorname{\mathit{coefficients}} = ![54, -1140, 11637, -54252, 33192, 658756, -1921212, -1566516, 12850374, -7108644, -35018232, 43506046, 38500440, -85687812, -200796, 75241308, -31685592, -25769200, 20878068, 213348, -3655770, 608916, 230904, -61761, -2790, 1800, -125]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Index zero multiplies the count at lag one. Index twenty-six multiplies the count at lag twenty-seven.

**Definition 1.2 (Scalar matrix readout).**

$$\forall D: \operatorname{\mathit{Nat}}, (\forall M: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Int}}\right), (\forall v: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\forall e: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\forall k: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{scalar}}\left(M, v, e, k\right) = \operatorname{\mathit{dotProduct}}\left(v, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left((M)^{k}, e\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.scalar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The row and column vectors use the same dimension as the integer transition matrix.

**Definition 1.3 (Signed scalar residual).**

$$\forall D: \operatorname{\mathit{Nat}}, (\forall M: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Int}}\right), (\forall v: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\forall e: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\forall t: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{residual}}\left(M, v, e, t\right) = \operatorname{\mathit{scalar}}\left(M, v, e, 30 + t\right) - \sum_{j: \operatorname{\mathit{Fin}}\left(27\right)} (\operatorname{\mathit{coefficients}}\left(j\right) \cdot \operatorname{\mathit{scalar}}\left(M, v, e, 29 - \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) + t\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The exponent is one less than the strip length. The scalar residual at offset zero corresponds to length thirty-one.

**Definition 1.4 (Signed row-vector residual).**

$$\forall D: \operatorname{\mathit{Nat}}, (\forall M: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Int}}\right), (\forall v: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\operatorname{\mathit{residualVector}}\left(M, v\right) = \operatorname{\mathit{forward}}\left(M, v, 30\right) - \sum_{j: \operatorname{\mathit{Fin}}\left(27\right)} ((\operatorname{\mathit{coefficients}}\left(j\right)) \cdot (\operatorname{\mathit{forward}}\left(M, v, 29 - \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.residualVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

The row-vector residual uses the initial vector and the transfer powers before applying the terminal readout.

**Theorem 1.5 (Transport of the residual).**

$$\forall D: \operatorname{\mathit{Nat}}, (\forall M: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Fin}}\left(D\right), \operatorname{\mathit{Int}}\right), (\forall v: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\forall e: (\operatorname{\mathit{Fin}}\left(D\right)) \to (\operatorname{\mathit{Int}}), (\forall t: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{residual}}\left(M, v, e, t\right) = \operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{residualVector}}\left(M, v\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left((M)^{t}, e\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.residual_as_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

Each lagged term has the same additional power. Distributivity moves that power after the signed sum.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.coefficients`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.residual`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.residualVector`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.residual_as_power`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual.scalar`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
