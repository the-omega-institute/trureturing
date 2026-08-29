# Local Spectral Floors

## Abstract

Parity sectors and the local positive cone determine the full spectral floor.

**Theorem 1.1 (Parity decomposition of the spectral infimum).**

$$\forall Even \in Type, Odd \in Type, evenEnergy \in Even \to \operatorname{Real}\left(\right), evenNormSq \in Even \to \operatorname{Real}\left(\right), oddEnergy \in Odd \to \operatorname{Real}\left(\right), oddNormSq \in Odd \to \operatorname{Real}\left(\right),\; \left(\operatorname{Zero}\left(Even\right) \land \left(\operatorname{Zero}\left(Odd\right) \land \left(\operatorname{Nontrivial}\left(Even\right) \land \left(\operatorname{Nontrivial}\left(Odd\right) \land \left(\operatorname{apply}\left(evenEnergy, 0\right) = 0 \land \left(\operatorname{apply}\left(oddEnergy, 0\right) = 0 \land \left(\operatorname{apply}\left(evenNormSq, 0\right) = 0 \land \left(\operatorname{apply}\left(oddNormSq, 0\right) = 0 \land \left(\left(\forall e \in Even,\; \left(\neg e = 0\right) \Rightarrow 0 < \operatorname{apply}\left(evenNormSq, e\right)\right) \land \left(\left(\forall o \in Odd,\; \left(\neg o = 0\right) \Rightarrow 0 < \operatorname{apply}\left(oddNormSq, o\right)\right) \land \left(\operatorname{BddBelow}\left(\left\{\exists e \in Even,\; \left(\neg e = 0\right) \land r = \operatorname{div}\left(\operatorname{apply}\left(evenEnergy, e\right), \operatorname{apply}\left(evenNormSq, e\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}\right) \land \operatorname{BddBelow}\left(\left\{\exists o \in Odd,\; \left(\neg o = 0\right) \land r = \operatorname{div}\left(\operatorname{apply}\left(oddEnergy, o\right), \operatorname{apply}\left(oddNormSq, o\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{let} fullValues = \left\{\exists e \in Even, o \in Odd,\; \left(\neg \operatorname{pair}\left(e, o\right) = \operatorname{pair}\left(0, 0\right)\right) \land r = \operatorname{div}\left(\operatorname{add}\left(\operatorname{apply}\left(evenEnergy, e\right), \operatorname{apply}\left(oddEnergy, o\right)\right), \operatorname{add}\left(\operatorname{apply}\left(evenNormSq, e\right), \operatorname{apply}\left(oddNormSq, o\right)\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}, \operatorname{let} evenValues = \left\{\exists e \in Even,\; \left(\neg e = 0\right) \land r = \operatorname{div}\left(\operatorname{apply}\left(evenEnergy, e\right), \operatorname{apply}\left(evenNormSq, e\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}, \operatorname{let} oddValues = \left\{\exists o \in Odd,\; \left(\neg o = 0\right) \land r = \operatorname{div}\left(\operatorname{apply}\left(oddEnergy, o\right), \operatorname{apply}\left(oddNormSq, o\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}, \operatorname{sInf}\left(fullValues\right) = \operatorname{min}\left(\operatorname{sInf}\left(evenValues\right), \operatorname{sInf}\left(oddValues\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/LocalSpectralFloor.parity_spectral_infimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full carrier is the even-odd product. Additivity of energy and squared norm makes every mixed Rayleigh quotient a positive weighted average of the two sector quotients, while pure-sector vectors attain both comparison infima.

**Theorem 1.2 (White-noise cone margin).**

$$\forall H \in Type, quadratic \in H \to \operatorname{Real}\left(\right), normSq \in H \to \operatorname{Real}\left(\right),\; \left(\operatorname{Zero}\left(H\right) \land \left(\operatorname{Nontrivial}\left(H\right) \land \left(\operatorname{apply}\left(quadratic, 0\right) = 0 \land \left(\operatorname{apply}\left(normSq, 0\right) = 0 \land \left(\left(\forall f \in H,\; \left(\neg f = 0\right) \Rightarrow 0 < \operatorname{apply}\left(normSq, f\right)\right) \land \operatorname{BddBelow}\left(\left\{\exists f \in H,\; \left(\neg f = 0\right) \land r = \operatorname{div}\left(\operatorname{apply}\left(quadratic, f\right), \operatorname{apply}\left(normSq, f\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{let} rayleighValues = \left\{\exists f \in H,\; \left(\neg f = 0\right) \land r = \operatorname{div}\left(\operatorname{apply}\left(quadratic, f\right), \operatorname{apply}\left(normSq, f\right)\right) \mid r \in \operatorname{Real}\left(\right)\right\}, \operatorname{let} admissibleFloors = \left\{\forall f \in H,\; 0 \le \operatorname{sub}\left(\operatorname{apply}\left(quadratic, f\right), \operatorname{mul}\left(lambda, \operatorname{apply}\left(normSq, f\right)\right)\right) \mid lambda \in \operatorname{Real}\left(\right)\right\}, \operatorname{sInf}\left(rayleighValues\right) = \operatorname{sSup}\left(admissibleFloors\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/LocalSpectralFloor.white_noise_cone_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible white-noise floor is exactly a lower bound of the nonzero Rayleigh-value set. The supremum of all such lower bounds is therefore the spectral infimum.

## References

- Truth anchor: `D5/S3/Weil/ZetaCore/LocalSpectralFloor.parity_spectral_infimum`
- Truth anchor: `D5/S3/Weil/ZetaCore/LocalSpectralFloor.white_noise_cone_margin`
