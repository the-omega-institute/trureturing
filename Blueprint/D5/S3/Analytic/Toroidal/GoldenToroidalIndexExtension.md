# Golden Toroidal Index Extension

## Abstract

A golden toroidal channel preserves pointwise nonvanishing, the window common-zero locus, and the frozen RH temperedness condition.

**Theorem 1.1 (The golden channel preserves nonvanishing and common zeros).**

$$\forall Index \in \operatorname{Type}\left(\right), Omega \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right), P \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), Pg \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), Tg \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right),\; \left(\left(\forall i \in Index, s \in \operatorname{Complex}\left(\right),\; P\left(i\right)\left(s\right) = xiReading\left(s\right) \times T\left(i\right)\left(s\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; s \in Omega \Rightarrow \left(\exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; Pg\left(s\right) = xiReading\left(s\right) \times Tg\left(s\right)\right)\right)\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; s \in Omega \Rightarrow \left(\exists j \in \operatorname{Sum}\left(Index, \operatorname{Unit}\left(\right)\right),\; Sum.elim\left(T, \operatorname{const}\left(Tg\right)\right)\left(j\right)\left(s\right) \ne 0\right)\right) \land \left\{\forall j \in \operatorname{Sum}\left(Index, \operatorname{Unit}\left(\right)\right),\; Sum.elim\left(P, \operatorname{const}\left(Pg\right)\right)\left(j\right)\left(\operatorname{val}\left(x\right)\right) = 0 \mid x \in \operatorname{Subtype}\left(Omega\right)\right\} = \left\{\forall i \in Index,\; P\left(i\right)\left(\operatorname{val}\left(x\right)\right) = 0 \mid x \in \operatorname{Subtype}\left(Omega\right)\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension.golden_toroidal_index_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original period family P factors pointwise as xiReading times the twist family T. Every point of Omega has an original twist chart with nonzero value. The added pair Pg and Tg is arbitrary apart from the same xiReading factorization.

The displayed Sum extension uses the original family on Index and the constant golden family on Unit. Its nonvanishing witness is the injected original witness. Applying the frozen toroidal common-zero theorem to both families identifies their window loci through the same xiReading zero set.

**Theorem 1.2 (The frozen RH right-hand predicate is extension-invariant).**

$$\forall Index \in \operatorname{Type}\left(\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), Tg \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right),\; \left(\forall s \in \operatorname{Complex}\left(\right),\; \exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \left(\forall j \in \operatorname{Sum}\left(Index, \operatorname{Unit}\left(\right)\right),\; \operatorname{completedRiemannZeta}\left(s\right) \times Sum.elim\left(T, \operatorname{const}\left(Tg\right)\right)\left(j\right)\left(s\right) = 0\right) \Rightarrow \operatorname{Re}\left(s - \frac{1}{2}\right) = 0\right) \Leftrightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; \left(\forall i \in Index,\; \operatorname{completedRiemannZeta}\left(s\right) \times T\left(i\right)\left(s\right) = 0\right) \Rightarrow \operatorname{Re}\left(s - \frac{1}{2}\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension.golden_toroidal_temperedness_rhs_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global pointwise nonvanishing of T also supplies global nonvanishing of the Sum extension. The frozen toroidal temperedness theorem equates each displayed right-hand predicate with the identical strip-native RH left side, so the two predicates are equivalent.

No Euler-germ nonvanishing, O-5 factorization, or identification of Tg with an Euler germ or Zqc is asserted. The result does not strengthen RH and does not use o5_independence.

## References

- Truth anchor: `D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension.golden_toroidal_index_extension`
- Truth anchor: `D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension.golden_toroidal_temperedness_rhs_iff`
- Dependency: [D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus](../Adelic/ToroidalCommonZeroLocus.md)
- Dependency: [D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion](../Adelic/ToroidalTemperednessCriterion.md)
