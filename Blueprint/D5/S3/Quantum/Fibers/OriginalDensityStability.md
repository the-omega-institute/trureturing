# Loss density stability on the original clock

## Abstract

Strong derivative error and a separate terminal phase certificate control the full original output.

Let c<1/2, 0<a<c and eta>0. Both (k,chi) and (l,psi) are original controls at the same base (c,c,1-2c) and horizon T>=0, with k(0)=l(0)=a. Both heights stay in [eta,c-eta]. For every t in [0,T], assume |k(t)-l(t)|<=delta. All integrals are Lebesgue integrals on (0,T], with their norm taken before integration. The original regularity alternatives imply absolute continuity and integrability of the derivatives; no common partition or derivative supremum bound is assumed.

Write e=derivativeError(T,k,l)=integral |k prime-l prime|, M=variation(T,l)=integral |l prime|, and D=variation(T,k)=integral |k prime|. Absolute continuity identifies these variations with total variation. Define budget(eta,delta,e,M)=B=e/eta+M delta/eta^2. The five original probabilities have slopes sigma=(1,-1,0,-1,1), in mode order 0,1,2,3,13. Every mode remains in the loss output, including constant-probability mode 2 and mode 13 at index four.

**Theorem 1.1 (Pointwise hazard error).**

$$\forall c \in Real, eta \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real),\; \left(\operatorname{positive}(eta) \land \operatorname{pointwisePairMargin}(t,eta,c,k,l)\right) \Rightarrow \operatorname{absHazardDifference}(c,k,l,t) \le \operatorname{absDerivativeDifference}(k,l,t)/eta+\operatorname{absDerivative}(l,t)\operatorname{absHeightDifference}(k,l,t)/\operatorname{square}(eta)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.hazard_pointwise_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two differentiable-value functions k,l and any real t at which both heights lie in [eta,c-eta], |hazard_k(t)-hazard_l(t)|<=|k prime(t)-l prime(t)|/eta+|l prime(t)| |k(t)-l(t)|/eta^2. The assertion is pointwise for totalized derivatives. The velocity dependence is continuous piecewise linear, and changing a reciprocal height costs at most the height error divided by eta squared.

**Theorem 1.2 (Accumulated hazard error).**

$$\forall c \in Real, T \in Real, eta \in Real, delta \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\operatorname{positive}(eta) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{uniformPairMargin}(T,eta,c,k,l) \land \operatorname{uniformHeightErrorLe}(T,k,l,delta)\right)\right)\right) \Rightarrow \operatorname{integralAbsHazardDifference}(c,T,k,l) \le \operatorname{budget}(eta,delta,\operatorname{derivativeError}(T,k,l),\operatorname{variation}(T,l))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.hazard_integral_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the common margin and height-error hypotheses, integral_0^T |hazard_k-hazard_l|<=B. The proof integrates the pointwise bound using the actual L1 derivative difference and the variation of l.

**Theorem 1.3 (Every survival prefix uses the full hazard error).**

$$\forall c \in Real, T \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \operatorname{inIcc}(t,0,T)\right) \Rightarrow \operatorname{absSurvivalDifference}(c,k,l,t) \le \operatorname{integralAbsHazardDifference}(c,T,k,l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.survival_integral_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two original controls and every t in [0,T], |S_k(t)-S_l(t)|<=integral_0^T |hazard_k-hazard_l|. No margin hypothesis is needed for this intermediate assertion. The hazard primitives are nonnegative; exp(-x) is one-Lipschitz for x>=0.

**Theorem 1.4 (Uniform survival error).**

$$\forall c \in Real, T \in Real, eta \in Real, delta \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\left(\operatorname{positive}(eta) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{uniformPairMargin}(T,eta,c,k,l) \land \operatorname{uniformHeightErrorLe}(T,k,l,delta)\right)\right)\right) \land \operatorname{inIcc}(t,0,T)\right) \Rightarrow \operatorname{absSurvivalDifference}(c,k,l,t) \le \operatorname{budget}(eta,delta,\operatorname{derivativeError}(T,k,l),\operatorname{variation}(T,l))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.survival_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The accumulated hazard estimate therefore gives |S_k(t)-S_l(t)|<=B for every t in [0,T] under the common margin and height-error assumptions.

**Theorem 1.5 (The exact loss-density estimate IS.28).**

$$\forall c \in Real, a \in Real, T \in Real, eta \in Real, delta \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real), i \in FinFive,\; \left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\operatorname{positive}(eta) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{uniformPairMargin}(T,eta,c,k,l) \land \operatorname{uniformHeightErrorLe}(T,k,l,delta)\right)\right)\right)\right)\right) \Rightarrow \operatorname{integralAbsLossDensityDifference}(c,a,T,k,l,i) \le (1+\operatorname{variation}(T,l)/eta+\operatorname{variation}(T,k))\operatorname{budget}(eta,delta,\operatorname{derivativeError}(T,k,l),\operatorname{variation}(T,l))+delta+\operatorname{derivativeError}(T,k,l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.loss_density_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original mode i, integral_0^T |lossDensity_i(k)-lossDensity_i(l)|<=(1+M/eta+D)B+delta+e. lossDensity_i is the original unnormalized source-family density, modeCoefficient_i p_i(a); OriginalReferenceOutputMeasure.source_coefficient identifies it with the source failureDensity, and native_coefficient_deriv identifies it almost everywhere with minus the derivative of S p_i(k). No common initial-height equality is needed for this scalar estimate itself.

Product differentiation gives the four differences -(S_k prime-S_l prime)p_i(k), -S_l prime(p_i(k)-p_i(l)), -(S_k-S_l)sigma_i k prime, and -S_l sigma_i(k prime-l prime). Their integrated absolute values are bounded by (1+M/eta)B, delta, DB and e. Here integral |S_k prime-S_l prime|<=(1+M/eta)B follows from S prime=-hazard S and integral hazard_l<=M/eta. Monotone survival gives integral |S_l prime|=1-S_l(T)<=1. Each p_i is at most one, each probability coordinate is one-Lipschitz, and |sigma_i|<=1. This proves the displayed constants for all five modes.

**Theorem 1.6 (No additional speed hypothesis is required).**

$$\forall c \in Real, T \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \Rightarrow \operatorname{variation}(T,k) \le \operatorname{variation}(T,l)+\operatorname{derivativeError}(T,k,l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.variation_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two original controls on the same horizon, D<=M+e follows by integrating |k prime|<=|l prime|+|k prime-l prime|. The variations are the integrals of the derivatives of the actual absolutely continuous heights.

**Theorem 1.7 (The full complete-output estimate).**

$$\forall c \in Real, a \in Real, T \in Real, eta \in Real, delta \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{evaluate}(k,0) = a \land \operatorname{evaluate}(l,0) = a\right)\right)\right)\right) \land \left(\operatorname{positive}(eta) \land \left(\operatorname{uniformPairMargin}(T,eta,c,k,l) \land \operatorname{uniformHeightErrorLe}(T,k,l,delta)\right)\right)\right) \Rightarrow \operatorname{completeOperationalDistance}(c,a,T,k,chi,l,psi) \le \operatorname{rootBudget}(c,a,\operatorname{budget}(eta,delta,\operatorname{derivativeError}(T,k,l),\operatorname{variation}(T,l)),delta)+\operatorname{phaseError}(c,T,k,chi,l,psi)+\operatorname{densityBudget}(c,a,eta,delta,\operatorname{derivativeError}(T,k,l),\operatorname{variation}(T,l),\operatorname{variation}(T,k),\operatorname{budget}(eta,delta,\operatorname{derivativeError}(T,k,l),\operatorname{variation}(T,l)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.complete_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put d_min=initialFloor(c,a)=min(a,c-a,1-2c)>0 and C=(1+M/eta+D)B+delta+e. For the actual complete operational distance of OriginalCompleteOutputStability, d_op<=sqrt((B+delta)/d_min)+phaseError+C/(2 d_min). phaseError=max_i |character_i(k,chi,T)-character_i(l,psi,T)| is a separate terminal character certificate. In the display, rootBudget=sqrt((B+delta)/d_min) and densityBudget=C/(2 d_min). The result combines the complete joint-output estimate IS.27, the loss-density estimate IS.28 and the terminal Kraus estimate IS.29, on the same common data.

**Theorem 1.8 (A common initial height gives uniform height control).**

$$\forall c \in Real, T \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{evaluate}(k,0) = \operatorname{evaluate}(l,0) \land \operatorname{inIcc}(t,0,T)\right)\right) \Rightarrow \operatorname{absHeightDifference}(k,l,t) \le \operatorname{derivativeError}(T,k,l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.height_error_le_derivativeError` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two original controls with k(0)=l(0), and every t in [0,T], |k(t)-l(t)|<=derivativeError(T,k,l). The fundamental theorem for absolutely continuous functions writes the difference as the integral of k prime-l prime on (0,t], which is bounded by the full L1 difference.

**Theorem 1.9 (Convergence of the complete operational output).**

$$\forall c \in Real, a \in Real, T \in Real, eta \in Real, M \in Real, k \in \operatorname{Sequence}(\operatorname{Function}(Real,Real)), chi \in \operatorname{Sequence}(\operatorname{Function}(Real,Real)), l \in \operatorname{Sequence}(\operatorname{Function}(Real,Real)), psi \in \operatorname{Sequence}(\operatorname{Function}(Real,Real)),\; \left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\operatorname{positive}(eta) \land \left(\operatorname{allCommonOriginalControls}(c,a,T,k,chi,l,psi) \land \left(\operatorname{allUniformPairMargins}(T,eta,c,k,l) \land \left(\operatorname{allVariationLe}(T,l,M) \land \left(\operatorname{derivativeErrorsTendstoZero}(T,k,l) \land \operatorname{terminalPhaseErrorsTendstoZero}(c,T,k,chi,l,psi)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{completeOperationalDistancesTendstoZero}(c,a,T,k,chi,l,psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDensityStability.complete_output_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix c,a,T,eta and a real bound M. Let (k_n,chi_n) and (l_n,psi_n) be two sequences of original controls on the common base and horizon, with both initial heights a and both heights in [eta,c-eta] for every n. Assume variation(T,l_n)<=M for every n, derivativeError(T,k_n,l_n) tends to zero, and phaseError(c,T,k_n,chi_n,l_n,psi_n) separately tends to zero. Then their completeOperationalDistance tends to zero, uniformly over all normalized positive joint trace-class inputs and unchanged Hilbert references in any fixed universe.

For convergence take delta_n=e_n, use D_n<=M+e_n and B_n=e_n/eta+M e_n/eta^2. The common initial probability floor is strictly positive. Continuity of the square root and the rational polynomial upper bound makes every term in the combined estimate tend to zero. Nonnegativity of the actual operational distance completes the squeeze argument. This proves a sufficient condition; it asserts neither necessity of derivative convergence nor acquisition of the phase certificate.

The actual output is the successful tensor Kraus congruence together with five Bochner failure-density measures on the same reference and physical time records. The result does not infer terminal phase control from height control, recover an intermediate phase waveform, grant access to old programme fields, construct an acquisition service, authorize a post-failure restart or establish physical realization.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.complete_error_bound`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.complete_output_convergence`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.hazard_integral_error`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.hazard_pointwise_error`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.height_error_le_derivativeError`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.loss_density_error`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.survival_error`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.survival_integral_error`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDensityStability.variation_le`
- Dependency: [D5/S3/Quantum/Fibers/OriginalCompleteOutputStability](OriginalCompleteOutputStability.md)
