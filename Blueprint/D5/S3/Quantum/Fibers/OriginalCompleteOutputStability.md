# The terminal quantum output and the full time record

## Abstract

Stability of the complete original instrument on a common arbitrary reference.

Fix c<1/2, 0<a<c, T>=0 and two original controls (k,chi) and (l,psi) at base (c,c,1-2c), with k(0)=l(0)=a. Both original regularity alternatives are included. The five probabilities, in the original order 0,1,2,3,13, are p(k)=(k,c-k,1-2c,c-k,k). S_k(t)=exp(-integral_0^t hazard(c,k,u) du) is the native survival. All integrals use the same physical time coordinate and Lebesgue measure.

The character z_i(t)=exp(-I integral_0^t phaseWeight((c,c,1-2c),k(u),i) chi prime(u) du) retains the original real phase integral. terminalDiagonal_i(t)=sqrt(S_k(t)) sqrt(p_i(k(t))/p_i(a)) z_i(t), and terminalKraus is its diagonal action on Blocks(Fin5,H). The existing tensor_diagonal identity identifies this action with the system Kraus map tensored with the identity on H. H is any complete complex Hilbert space; separability and product-state assumptions are absent.

For a common positive trace-class rho on Blocks(Fin5,H), terminalOutput is the actual terminalKraus rho terminalKraus-adjoint. phasedJump_i is the literal absorbing jump composed with the transported character diagonal. phasedFailure is its actual trace-class congruence, taking values in Blocks(Fin6,H), with absorbing coordinate f=5. completeDistance is one half of the sum of the terminal output difference norm and, over all five modes, the time integral of the norm of the density difference. The norm is taken before integrating time. Thus arbitrary Borel time events and the unchanged reference are retained.

**Theorem 1.1 (The height retains original admissibility).**

$$\forall c \in Real, T \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real),\; \operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \Rightarrow \operatorname{OriginalControl}(\operatorname{base}(c),T,k,\operatorname{zeroFunction}())$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.height_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any original (k,chi), replacing chi by the constant zero function gives an original control on the same base and horizon. Absolute continuity of k follows from either original regularity alternative. This permits direct use of the existing native mode balance theorem without changing k or its clock.

**Theorem 1.2 (The failure congruence is phase independent).**

$$\forall c \in Real, a \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}(\operatorname{Blocks}(FinFive,H)), i \in FinFive,\; \operatorname{Positive}(rho) \Rightarrow \operatorname{liveFailureOperator}(c,a,k,i,rho,t) = \operatorname{phasedKrausCongruence}(c,a,k,chi,t,i,rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.phased_failure_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real c,a,t, every k,chi, every original mode i and every positive trace-class rho on the same Blocks(Fin5,H), liveFailure_i(t) equals phasedJump_i(t) rho phasedJump_i(t)-adjoint. The jump row has one nonzero coordinate, so composing with the diagonal multiplies it by z_i(t). The character has modulus one and cancels inside the congruence. The terminal phase remains in terminalOutput.

**Theorem 1.3 (Each surviving mode is a contraction).**

$$\forall c \in Real, a \in Real, T \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), i \in FinFive,\; \left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \left(\operatorname{evaluate}(k,0) = a \land \operatorname{inIcc}(t,0,T)\right)\right)\right)\right) \Rightarrow \operatorname{survivingModeMass}(c,k,t,i) \le \operatorname{p}(c,a,i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.native_mass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t in [0,T] and i in Fin5, native mode balance and nonnegativity of the integrated squared jump amplitude give S_k(t)p_i(k(t))<=p_i(a). Consequently every successful diagonal entry has modulus at most one. The assertion uses the common initial height; survival<=1 alone would not establish this contraction.

**Theorem 1.4 (The complete distance for any common positive joint input).**

$$\forall c \in Real, a \in Real, T \in Real, b \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real), H \in CompleteComplexHilbertSpace, rho \in \operatorname{TraceClass}(\operatorname{Blocks}(FinFive,H)),\; \left(\left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{evaluate}(k,0) = a \land \operatorname{evaluate}(l,0) = a\right)\right)\right)\right) \land \left(\operatorname{Positive}(rho) \land \operatorname{allDensityErrorsLe}(c,a,T,k,l,b)\right)\right) \Rightarrow \operatorname{completeDistance}(c,a,T,k,chi,l,psi,rho) \le (\operatorname{krausError}(c,a,T,k,chi,l,psi)+b/2)\operatorname{norm}(rho)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.complete_output_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary H and positive trace-class rho, and every real b with densityError_i<=b for all i, completeDistance<= (krausError+b/2) norm(rho). Here lossDensity_i=modeCoefficient_i p_i(a), densityError_i=integral_0^T |lossDensity_i(k)-lossDensity_i(l)|/p_i(a), and krausError is the operator norm of the difference of the actual terminal Kraus maps on the original five-dimensional system. The result is unnormalized and retains entangled inputs.

**Theorem 1.5 (The operational estimate IS.27).**

$$\forall c \in Real, a \in Real, T \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{evaluate}(k,0) = a \land \operatorname{evaluate}(l,0) = a\right)\right)\right)\right) \Rightarrow \operatorname{completeOperationalDistance}(c,a,T,k,chi,l,psi) \le \operatorname{krausError}(c,a,T,k,chi,l,psi)+\operatorname{maxDensityError}(c,a,T,k,l)/2$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.complete_operational_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

completeOperationalDistance is the supremum of completeDistance over all complete complex Hilbert references in any fixed universe and all positive joint trace-class inputs of trace norm one. The joint-input estimate gives d_op<=kappa+(max_i densityError_i)/2, with exactly the coefficient one on kappa. A one-dimensional reference embedded in a live coordinate proves the set of inputs is nonempty.

**Theorem 1.6 (The operational distance is nonnegative).**

$$\forall c \in Real, a \in Real, T \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{evaluate}(k,0) = a \land \operatorname{evaluate}(l,0) = a\right)\right)\right)\right) \Rightarrow 0 \le \operatorname{completeOperationalDistance}(c,a,T,k,chi,l,psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.complete_operational_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same common initial-height and original-control hypotheses, the operational supremum is bounded above and contains the distance of a normalized live input. Each norm integral is nonnegative, so d_op>=0. This supplies the lower bound for convergence by squeezing.

**Theorem 1.7 (Survival never exceeds one).**

$$\forall c \in Real, T \in Real, t \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real),\; \left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{inIcc}(t,0,T)\right) \Rightarrow \operatorname{survival}(c,k,t) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.survival_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original (k,chi) and every t in [0,T], S_k(t)<=1. Native bounds put the height strictly between zero and c, so each term in its hazard is nonnegative.

**Theorem 1.8 (Every original probability is at most one).**

$$\forall c \in Real, x \in Real, i \in FinFive,\; \left(\operatorname{cLessHalf}(c) \land \operatorname{initialInterior}(x,c)\right) \Rightarrow \operatorname{p}(c,x,i) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.probability_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c<1/2, 0<x<c and every mode i, positivity and the original probability sum give p_i(x)<=1.

**Theorem 1.9 (Every probability coordinate is nonexpansive).**

$$\forall c \in Real, x \in Real, y \in Real, i \in FinFive,\; \operatorname{True}() \Rightarrow \operatorname{absProbabilityDifference}(c,x,y,i) \le \operatorname{absDifference}(x,y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.probability_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real c,x,y and all five original modes, |p_i(x)-p_i(y)|<=|x-y|. Their slopes are 1,-1,0,-1,1, including the constant mode 2 and mode 13 at index four.

**Theorem 1.10 (The terminal amplitude and character estimate IS.29).**

$$\forall c \in Real, a \in Real, T \in Real, B \in Real, delta \in Real, k \in \operatorname{Function}(Real,Real), chi \in \operatorname{Function}(Real,Real), l \in \operatorname{Function}(Real,Real), psi \in \operatorname{Function}(Real,Real),\; \left(\left(\operatorname{cLessHalf}(c) \land \left(\operatorname{initialInterior}(a,c) \land \left(\left(\operatorname{OriginalControl}(\operatorname{base}(c),T,k,chi) \land \operatorname{OriginalControl}(\operatorname{base}(c),T,l,psi)\right) \land \left(\operatorname{evaluate}(k,0) = a \land \operatorname{evaluate}(l,0) = a\right)\right)\right)\right) \land \left(\operatorname{terminalSurvivalErrorLe}(c,T,k,l,B) \land \operatorname{terminalHeightErrorLe}(T,k,l,delta)\right)\right) \Rightarrow \operatorname{krausError}(c,a,T,k,chi,l,psi) \le \operatorname{maxRootMassError}(c,a,B,delta)+\operatorname{terminalPhaseError}(c,T,k,chi,l,psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.terminal_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition to the common control hypotheses, suppose |S_k(T)-S_l(T)|<=B and |k(T)-l(T)|<=delta. Then kappa<=max_i sqrt((B+delta)/p_i(a))+max_i |z_i(T)-w_i(T)|. The terminal phase error is an independent certificate. The amplitude difference uses |S_k p_i(k)-S_l p_i(l)|<=B+delta and the square-root inequality |sqrt(x)-sqrt(y)|<=sqrt(|x-y|). Contractivity bounds the coefficient of the character difference by one.

The terminal proof writes A rho A-adjoint minus B rho B-adjoint as (A-B) rho A-adjoint plus B rho (A-B)-adjoint. The general trace-class ideal estimate bounds both mixed products, including nonpositive products, by their operator norms times norm(rho). The diagonal amplification bound holds on arbitrary H. The failure contribution is exactly sum_i densityError_i norm(rho_ii), where rho_ii is the compression of that same rho. Positivity is used only for these diagonal blocks and their trace partition sum_i norm(rho_ii)=norm(rho).

Terminal characters are not recovered from height data. No relative phase waveform, phase unwrapping, acquisition service, restart permission, physical realization or full programme reconstruction follows from these estimates.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.complete_operational_bound`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.complete_operational_nonneg`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.complete_output_bound`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.height_control`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.native_mass_le`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.phased_failure_actual`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.probability_difference`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.probability_le_one`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.survival_le_one`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalCompleteOutputStability.terminal_error_bound`
- Dependency: [D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass](OriginalReferenceRepeatedMass.md)
- Dependency: [D5/S3/TotalVariation/Hellinger](../../TotalVariation/Hellinger.md)
