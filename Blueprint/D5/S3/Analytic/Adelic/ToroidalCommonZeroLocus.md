# Toroidal Common Zero Locus

## Abstract

Pointwise nonvanishing quadratic twists identify the common period-zero locus with the completed-zeta zero locus on the regular spectral domain.

**Theorem 1.1 (All quadratic-period readouts have exactly the xi common zeros).**

$$\forall Index \in \operatorname{Type}\left(\right), Omega \in \operatorname{Set}\left(\operatorname{Complex}\left(\right)\right), P \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\left(\forall i \in Index, s \in \operatorname{Complex}\left(\right),\; P\left(i\right)\left(s\right) = xiReading\left(s\right) \times T\left(i\right)\left(s\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, Omega\right) \Rightarrow \left(\exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right)\right)\right) \Rightarrow \left\{\forall i \in Index,\; P\left(i\right)\left(\operatorname{val}\left(x\right)\right) = 0 \mid x \in \operatorname{Subtype}\left(Omega\right)\right\} = \left\{xiReading\left(\operatorname{val}\left(x\right)\right) = 0 \mid x \in \operatorname{Subtype}\left(Omega\right)\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus.toroidal_common_zero_locus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set Omega is the source's regular spectral region. Period and twist are complex-valued families on the exact complex carrier, and the displayed factorization constructs every period readout as xiReading times its quadratic twist.

Pointwise nonvanishing means that every point of Omega has at least one twist chart on which cancellation by the twist is valid. The common period-zero set is therefore exactly the xiReading zero set on the subtype Omega.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus.toroidal_common_zero_locus`
- Dependency: [D5/S3/Analytic/Adelic/ToroidalCechCompletion](ToroidalCechCompletion.md)
