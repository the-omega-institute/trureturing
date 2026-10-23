# Five Mode Periodic Diameter Obstruction

## Abstract

A complete law generated on a periodic B orbit cannot attain the diameter midpoint of two unequal-holding startup endpoints.

The source is FiniteStartFiveModeSource: p,q,r are positive and p+q+r<1, a=1-p-q and b=1-r. The visible alphabet is Fin 4 in the order 0,1,B,3, with B=2. First exits from source mode 2 lie in {1,3}; those from mode 4 lie in {0}. Write u=min(a,b), v=max(a,b). When a differs from b, 0<u<v<1. The dominant law is the pure source mode with holding v. The oriented mixture G(D) gives weight D to the other mode.

A GeneratedObserver has a total deterministic update and a normalized nonnegative emission row at every configuration. Its complete finite-word law uses that same update after each generated symbol. The theorem allows any carrier Z, so in particular every finite carrier, and every positive integer period L. Only the B update at the chosen starting configuration is periodic. Nothing restricts the configurations or the emissions after an exit. Forecast zeros remain allowed.

**Definition 1.1 (survival).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall z \in Z,\; \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{survival}\left(O, z, 0\right) = 1 \land \operatorname{survival}\left(O, z, n + 1\right) = \operatorname{row}\left(O, z, \operatorname{B}\left(\right)\right) \cdot \operatorname{survival}\left(O, \operatorname{update}\left(O, z, \operatorname{B}\left(\right)\right), n\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter.survival` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

survival(O,z,n) is the probability of the all-B generated word of length n.

**Definition 1.2 (exitCoefficient).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall z \in Z,\; \forall n \in \operatorname{Nat}\left(\right),\; \forall t \in \operatorname{Bool}\left(\right),\; \left(\operatorname{exitCoefficient}\left(O, z, 0, \operatorname{true}\left(\right)\right) = \operatorname{row}\left(O, z, 0\right) \land \operatorname{exitCoefficient}\left(O, z, 0, \operatorname{false}\left(\right)\right) = \operatorname{row}\left(O, z, 1\right) + \operatorname{row}\left(O, z, 3\right)\right) \land \operatorname{exitCoefficient}\left(O, z, n + 1, t\right) = \operatorname{row}\left(O, z, \operatorname{B}\left(\right)\right) \cdot \operatorname{exitCoefficient}\left(O, \operatorname{update}\left(O, z, \operatorname{B}\left(\right)\right), n, t\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter.exitCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the probability of n B symbols followed by a first exit in {0} for true or {1,3} for false. All subsequent words are summed over the complete normalized continuation law.

**Theorem 1.3 (periodic diameter obstruction).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall D \in \operatorname{Real}\left(\right),\; \forall z \in Z,\; \forall L \in \operatorname{Nat}\left(\right),\; \left(\left(\left(\left(\left(\left(\left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \land 0 < L\right) \land \operatorname{iterateAt}\left(\operatorname{Bupdate}\left(O\right), L, z\right) = z\right) \land 0 < D\right) \land D < 1\right) \land \operatorname{profileDistance}\left(\operatorname{dominantLaw}\left(p, q, r\right), \operatorname{generatedLaw}\left(\operatorname{update}\left(O\right), \operatorname{row}\left(O\right), z\right)\right) \le \frac{D}{2}\right) \land \operatorname{profileDistance}\left(\operatorname{orientedMixture}\left(p, q, r, D\right), \operatorname{generatedLaw}\left(\operatorname{update}\left(O\right), \operatorname{row}\left(O\right), z\right)\right) \le \frac{D}{2}\right) \Rightarrow \operatorname{False}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter.periodic_diameter_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete generated profile cannot satisfy the two stated distance bounds. The period is an iterate of the total B update, independently of any source-observer recurrent class.

At horizon H, coarsen each word to its first-exit time and category, or to its all-B survivor. Induction on H bounds the resulting sum of absolute coefficient differences by the original word sum, for every real linear combination A*F2+C*F4 and every real coefficient E multiplying the generated law. On each exit branch normalization and the absolute-sum inequality suffice; the generated continuation need not equal the source continuation. The survivor coefficient A*a^H+C*b^H-E*survival(O,z,H) remains present.

For the dominant and G(D) endpoints, the finite coarsened distance is D*(1-u^H). The triangle defect at any fixed exit coordinate is nonnegative and is bounded by the total defect of a longer finite partition. The two radius assumptions and the endpoint limit force that fixed coordinate defect to zero. Hence the generated dominant exit coefficient lies between (1-D)*(1-v)*v^n and (1-v)*v^n, and the minority coefficient lies between zero and D*(1-u)*u^n. This limit argument does not assert finite-horizon triangle equality.

The minority exit coefficients cannot all vanish: their finite sum is exactly the generated first-minority-exit event mass, whereas the corresponding G(D) event has mass D*(1-u^H). Its event-gap bound and the limit would give D<=D/2. Thus some minority coefficient is positive. This argument retains every finite survivor and does not assume almost-sure exit of the generated process.

Put gamma=survival(O,z,L). The actual product recursion and periodic update give exitCoefficient(O,z,m*L+n,t)=gamma^m*exitCoefficient(O,z,n,t). The positive dominant lower bound makes gamma positive and forces v^L<=gamma by the existing uniform geometric domination theorem. The positive minority coefficient and its upper bound force gamma<=u^L. Since L>0 and u<v, these inequalities contradict each other. The geometric domination theorem is the original NativePeriodicWordLaw.geometric_rate_bound with no additional source parameter assumptions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter.exitCoefficient`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter.periodic_diameter_obstruction`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter.survival`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw](../../Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws](FiveModeSelfGeneratedLaws.md)
