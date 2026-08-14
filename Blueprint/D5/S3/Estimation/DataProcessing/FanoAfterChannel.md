# Fano Error Bounds after Finite Channels

## Abstract

Finite Fano inversion and Markov data processing give estimator-error floors after arbitrary finite garbling and after explicit row-stochastic channels.

**Theorem 1.1 (Markov garbling preserves the pre-channel Fano floor).**

$$\begin{gathered}\forall X, Y, Z,\\p: X\times (Y\times Z)\to \mathbb{R}, g: Z\to X,\\((\forall x, y, z, 0\leq p(x, (y, z))) \land \sum _{x, y, z} p(x, (y, z))= 1) \land \\(\forall x, y, z, p(x, (y, z))\times \operatorname{marginal}(\operatorname{yFirstLaw}(p))(y)= \operatorname{xyProjection}(p)(x, y)\times \operatorname{xzProjection}(\operatorname{yFirstLaw}(p))(y, z)) \land \\(\forall x, \operatorname{marginal}(p)(x)= \frac{1}{\operatorname{card}(X)}) \land 2\leq \operatorname{card}(X)) \Rightarrow \\1- \frac{\operatorname{mutualInformation}(\operatorname{xyProjection}(p))+ \log 2}{\log \operatorname{card}(X)}\leq \sum _{x, z: g(z)\neq x} \operatorname{xzProjection}(p)(x, z).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/FanoAfterChannel.fano_error_probability_lower_bound_of_markov` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative law on the right-nested product X times (Y times Z). The theorem keeps the Markov assumption in the repository's raw cross-multiplied form: p(x,y,z) times the Y marginal equals the XY marginal times the YZ marginal. No conditional division or named Markov predicate is introduced.

The estimator sees only Z. To apply the frozen Fano endpoint, the proof swaps the XZ projection into the observation-first order Z times X. It verifies normalization after that swap, transports the uniform X marginal, and uses mutual-information symmetry to identify the swapped information term with I(X;Z).

Fano then lower-bounds the estimator's XZ error using I(X;Z). The Markov data-processing inequality gives I(X;Z) <= I(X;Y), and positivity of log(card X), supplied exactly by 2 <= card X, makes substitution of the larger pre-garbling information budget order-correct.

**Theorem 1.2 (Row-stochastic channels inherit the pre-channel Fano floor).**

$$\begin{gathered}\forall pXY, W, g,\\((\forall x, y, 0\leq pXY(x, y)) \land \sum _{x, y} pXY(x, y)= 1) \land \\(\forall y, z, 0\leq W(y, z)) \land (\forall y, \sum _{z} W(y, z)= 1) \land \\(\forall x, \operatorname{marginal}(pXY)(x)= \frac{1}{\operatorname{card}(X)}) \land 2\leq \operatorname{card}(X)) \Rightarrow \\1- \frac{\operatorname{mutualInformation}(pXY)+ \log 2}{\log \operatorname{card}(X)}\leq \sum _{x, z: g(z)\neq x} \sum _{y} pXY(x, y)\times W(y, z).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/FanoAfterChannel.fano_error_probability_lower_bound_after_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit channel law is p(x,y,z) = pXY(x,y) W(y,z). The input joint pXY is a normalized nonnegative law with a uniform X marginal, while W is pointwise nonnegative and every row sums to one. The estimator g is otherwise arbitrary.

Row normalization does all of the transport work. Summing the generated joint over Z recovers pXY, so the generated law has total mass one, its X marginal remains uniform, and its XY projection has exactly the pre-channel mutual information appearing in the displayed floor.

The existing channel lemma supplies the raw Markov identity for the generated joint. Applying the preceding theorem therefore bounds the error mass of every estimator based on the garbled output Z by the information available before the channel. No invertibility, positivity of individual channel entries, or estimator construction is assumed.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/FanoAfterChannel.fano_error_probability_lower_bound_after_channel`
- Truth anchor: `D5/S3/Estimation/DataProcessing/FanoAfterChannel.fano_error_probability_lower_bound_of_markov`
- Dependency: [D5/S3/Entropy/MutualInformationSymm](../../Entropy/MutualInformationSymm.md)
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](../../Entropy/Submodularity/MarkovDataProcessing.md)
- Dependency: [D5/S3/Estimation/FanoErrorBound](../FanoErrorBound.md)
