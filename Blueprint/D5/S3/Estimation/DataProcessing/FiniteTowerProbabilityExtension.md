# Probability Extension Without Surjective Carrier Bonds

## Abstract

Compatible finite probability laws extend uniquely to the actual threads of an arbitrary total tower.

**Theorem 1.1 (The original compatible laws have one Borel extension).**

$$\exists!\mu\in\operatorname{Prob}\left(\operatorname{Thread}\left(B, q\right)\right),\forall l,\operatorname{project}\left(\mu, l\right) = \operatorname{theta}\left(l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension.exists_unique_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural level l, B_l is finite and nonempty, with the discrete topology and its Borel measurable structure. The bonding function q_l maps B_(l+1) to B_l and is defined everywhere. It need not be surjective.

Thread B q is the actual subtype of sequences x with q_l(x_(l+1))=x_l at every level. Its measurable structure is the Borel structure inherited from the countable product of finite discrete spaces. No symbol is removed from B_l.

The input theta_l is a probability measure on B_l, with exact pushforward compatibility along q_l. Probabilities may have arbitrary real masses and may assign zero mass to symbols. The conclusion supplies a unique probability mu on Thread B q whose l-th coordinate pushforward is theta_l for every l.

The construction places each finite law on its compatible finite prefix inside the full prefix alphabet. Dropping the last prefix coordinate is surjective. The existing surjective-tower theorem supplies the auxiliary probability.`D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension.exists_unique_probability_extension`

Each auxiliary prefix has full measure in the image of its compatible-prefix embedding. The countable intersection of these full-measure constraints concentrates the decoded product law on the original thread equations. Restriction through the measurable subtype embedding returns the original thread probability, with the required coordinate laws.

Equal coordinate laws force zero full-event total variation, hence equality of the two probabilities on every measurable event. The event-TV supplier does not require surjective original bonds.`D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.total_variation_eq_iSup_level`

Uniqueness applies to the extension of the prescribed compatible family. It does not say that every prescribed single-level law extends, or that a nearest feasible law is unique. Only the declared Borel thread event domain is asserted; no arbitrary enlargement is included.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension.exists_unique_extension`
- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.total_variation_eq_iSup_level`
- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension.exists_unique_probability_extension`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension](InverseLimitProbabilityExtension.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
