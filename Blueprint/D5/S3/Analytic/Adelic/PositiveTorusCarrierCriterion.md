# Positive Torus Carrier Criterion

## Abstract

A nonnegative weighted torus period whose nontrivial zeros are critical and whose auxiliary factor is regular forces all nontrivial zeta zeros onto the midline.

**Theorem 1.1 (A regular positive torus carrier implies the critical-line criterion).**

$$\begin{aligned}\forall Index, Torus \in \operatorname{Type}\left(\right), \operatorname{MeasurableSpace}\left(Torus\right)\\a: Index \to \operatorname{NNReal}\left(\right), muD: Index \to \operatorname{Measure}\left(Torus\right)\\EStar: Torus \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), e, twistedCompleted: Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right)\\mu := \operatorname{measureSum}\left((i \mapsto \operatorname{toENNReal}\left(a\left(i\right)\right) \cdot muD\left(i\right))\right)\\Fmu := (s \mapsto \operatorname{integral}\left((z \mapsto EStar\left(z\right)\left(s\right)), mu\right))\\Gmu := (s \mapsto \operatorname{tsum}\left((i \mapsto \operatorname{toComplex}\left(a\left(i\right)\right) \times e\left(i\right)\left(s\right) \times twistedCompleted\left(i\right)\left(s\right))\right))\\Hplus := \left\{\frac{1}{2} < \operatorname{re}\left(s\right) \mid s \in \operatorname{Complex}\left(\right)\right\}\\((\forall s \in \operatorname{Complex}\left(\right),\; \left(\operatorname{AnalyticAt}\left(\operatorname{Complex}\left(\right), Gmu, s\right) \land Gmu\left(s\right) \neq 0\right) \Rightarrow Fmu\left(s\right) = \operatorname{completedRiemannZeta}\left(s\right) \times Gmu\left(s\right)) \land (\forall s \in \operatorname{Complex}\left(\right),\; \left(Fmu\left(s\right) = 0 \land \left(0 < \operatorname{re}\left(s\right) \land \operatorname{re}\left(s\right) < 1\right)\right) \Rightarrow \operatorname{re}\left(s\right) = \frac{1}{2}) \land \operatorname{AnalyticOnNhd}\left(\operatorname{Complex}\left(\right), Gmu, Hplus\right) \land (\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{mem}\left(s, Hplus\right) \Rightarrow Gmu\left(s\right) \neq 0)) \Rightarrow \forall rho \in \operatorname{Complex}\left(\right),\; \operatorname{IsNontrivialZero}\left(rho\right) \Rightarrow \operatorname{re}\left(rho\right) = \frac{1}{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/PositiveTorusCarrierCriterion.positive_torus_carrier_condition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measure mu is the literal Measure.sum of the supplied period measures scaled by NNReal weights. The period Fmu is the Bochner integral of the supplied Eisenstein family against mu. The auxiliary factor Gmu is the literal weighted tsum of the local and twisted-completion factors.

The Hecke factorization is required whenever Gmu is analytic and nonzero at the evaluation point. The two source regularity clauses provide exactly those facts on the open right half-plane, so every right-half completed-zeta zero becomes a zero of Fmu and hence lies on the midline by the period-zero premise.

The frozen completed-zeta zero theorem supplies the canonical nontrivial zeta carrier. Frozen conjugate reflection transports any left-half zero to the right half and completes the global conclusion.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/PositiveTorusCarrierCriterion.positive_torus_carrier_condition`
