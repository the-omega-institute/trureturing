# Toroidal Temperedness Criterion

## Abstract

The strip-native Riemann hypothesis is equivalent to temperedness of every nontrivial toroidal Eisenstein parameter.

**Theorem 1.1 (RH is equivalent to toroidal Eisenstein temperedness).**

$$\forall Index \in \operatorname{Type}\left(\right), T \in Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\; \left(\forall s \in \operatorname{Complex}\left(\right),\; \exists i \in Index,\; T\left(i\right)\left(s\right) \ne 0\right) \Rightarrow \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{IsNontrivialZero}\left(s\right) \Rightarrow \operatorname{Re}\left(s\right) = \frac{1}{2}\right) \Leftrightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; \left(\forall i \in Index,\; \operatorname{completedRiemannZeta}\left(s\right) \times T\left(i\right)\left(s\right) = 0\right) \Rightarrow \operatorname{Re}\left(s - \frac{1}{2}\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion.rh_iff_all_toroidal_eisenstein_tempered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left side is the canonical nontrivial strip-zero formulation. On the right, toroidal invisibility is stated directly by vanishing of every completed-zeta-times-twist period.

Pointwise twist nonvanishing makes simultaneous period vanishing equivalent to a completed-zeta zero. The frozen completed-zeta zero-locus theorem then identifies exactly the strip zeros.

The normalized principal-series parameter is s minus one half. Its real part vanishes exactly on the critical line, which is the displayed temperedness condition.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion.rh_iff_all_toroidal_eisenstein_tempered`
