# The retained joint cq output and common downstream execution

## Abstract

Common realized downstream actions on the actual complete original quantum output.

Fix c<1/2, 0<a<c, a finite horizon T>=0 and two original controls (k,chi),(l,psi) on the same base (c,c,1-2c). Both original regularity alternatives, all real phase lifts and signed winding sectors remain in scope. For any complete complex Hilbert reference H and any common positive joint trace-class rho on Blocks(Fin5,H), output packs the literal terminalOutput and all five phasedFailure densities on the original absorbing Blocks(Fin6,H) carrier, with the exact record measure volume restricted to (0,T]. No normalization, separability or finite-rank assumption is used.

Native mode balance applied through height_control proves coefficient integrability for every original control. The original phasedFailure_eq identifies each density with modeCoefficient_i(t) times the same fixed positive absorbing embedding of rho_ii. The actual paired difference therefore has scalar coefficients h_i=modeCoefficient_i(k)-modeCoefficient_i(l) multiplying the same positive operator blocks. RecordedOutput.fixed_block_decomposition applies to this input difference; it imposes no fixed-block restriction on the downstream result. The terminal difference is Hermitian because both actual Kraus congruences are positive.

**Theorem 1.1 (The complete output distance is the cq norm).**

$$\forall H \in CompleteComplexHilbertSpace, c \in Real, a \in Real, T \in Real, k \in RealPath, chi \in RealPath, l \in RealPath, psi \in RealPath, rho \in JointTraceClass,\; \left(cLessHalf\left(c\right) \land \left(initialInterior\left(a, c\right) \land \left(OriginalControl\left(c, T, k, chi\right) \land \left(OriginalControl\left(c, T, l, psi\right) \land Positive\left(rho\right)\right)\right)\right)\right) \Rightarrow halfNormDifference\left(output\left(c, a, T, k, chi, rho\right), output\left(c, a, T, l, psi, rho\right)\right) = completeDistance\left(c, a, T, k, chi, l, psi, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDownstreamOutput.output_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such pair and positive joint input, norm(output(k,chi)-output(l,psi))/2 equals the existing completeDistance exactly. The additive WithLp/PiLp norms give the terminal trace norm plus the sum over all five modes of the integral of the density difference trace norm. Integrable.toL1 and its almost-everywhere representatives justify the equality before integration. Signed densities are not integrated before taking norms. At T=0 the record measure is zero, so the same statement includes the zero horizon.

**Theorem 1.2 (Common lawful realized executions cannot increase this distance).**

$$\forall H \in CompleteComplexHilbertSpace, c \in Real, a \in Real, T \in Real, k \in RealPath, chi \in RealPath, l \in RealPath, psi \in RealPath, rho \in JointTraceClass, W \in RealSeminormedSpace, target \in PositiveNormMassDistanceTarget, run \in ActualJointExecution, allowed \in IndependentLegalityPredicate, program \in Program, context \in CommonPolicyReferencePermissionExternalInputs, R \in RealizationWitness,\; \left(\left(cLessHalf\left(c\right) \land \left(initialInterior\left(a, c\right) \land \left(OriginalControl\left(c, T, k, chi\right) \land \left(OriginalControl\left(c, T, l, psi\right) \land Positive\left(rho\right)\right)\right)\right)\right) \land Realization\left(target, run, allowed, program, context, R\right)\right) \Rightarrow targetDistance\left(run\left(program, context, output\left(c, a, T, k, chi, rho\right)\right), run\left(program, context, output\left(c, a, T, l, psi, rho\right)\right)\right) \le completeDistance\left(c, a, T, k, chi, l, psi, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDownstreamOutput.downstream_distance_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Target carries the actual target positive cone predicate, a continuous real-linear mass, norm=mass on positive outputs, and the exact equality of its declared complete distance with half the norm of a difference. A Realization is indexed by an independently specified run(program,context,q) and an independent allowed(program,context) predicate. It supplies the permission proof, one real-linear action, agreement of that action with run on every joint input, positivity on the entire joint cone and mass nonincrease on that cone. The same program and the same Context, containing acquired-record policy, references, permissions and external inputs, are used in both runs. The theorem derives target.distance(run(output(k)),run(output(l)))<=completeDistance. It assumes neither contraction nor an operator norm bound. The map laws are applied to both constructed positive norming parts, not just the two normalized instrument outputs.

**Theorem 1.3 (The uniform downstream IS.27 bound).**

$$\forall c \in Real, a \in Real, T \in Real, k \in RealPath, chi \in RealPath, l \in RealPath, psi \in RealPath, W \in JointInputIndexedRealSeminormedSpaces, target \in TargetFamily, run \in ActualJointExecutionFamily, allowed \in IndependentLegalityPredicate, program \in Program, context \in CommonPolicyReferencePermissionExternalInputs, R \in RealizationFamily,\; \left(CommonOriginalPairWithInitialHeight\left(c, a, T, k, chi, l, psi\right) \land AllJointInputRealizations\left(target, run, allowed, program, context, R\right)\right) \Rightarrow sSup\left(ActualDownstreamDistances\left(target, run, program, context\right)\right) \le add\left(krausError\left(c, a, T, k, chi, l, psi\right), halfMaxDensityError\left(c, a, T, k, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalDownstreamOutput.downstream_operational_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume in addition k(0)=l(0)=a. For every normalized joint input and arbitrary unchanged complete complex Hilbert reference, supply a target and an actual common execution realization of the same program and context. The supremum of these downstream complete distances is at most kappa+(max_i b_i)/2, with the exact krausError and densityError of IS.27. Each downstream distance is bounded by its corresponding completeDistance. Native boundedness of the original input set justifies comparison with its supremum, and complete_operational_bound then supplies IS.27 directly. A protocol family independent of rho is a special case; the same-input comparison always uses one common action in both experiments.

This semantic interface permits record-conditioned adaptive policies with different observed branches; no finite-round, finite-outcome, matrix or reference-dimension restriction occurs. It does not construct arbitrary program semantics. A separately specified class of legal programs is covered only when its actual executions have these witnesses. Complete positivity, normality, countable additivity, reference amplification and record measurability must be justified by each actual realization where applicable; generic positivity grants no access permission. Limiting procedures require their actual existence and convergence evidence.

Mass preservation is a special case of mass nonincrease. A trace-nonincreasing branch is compared with its actual unnormalized output; a complete output retains every required failure/abort successor. No normalized-postselection claim follows. A fixed independent common external state requires its actual positive mass-preserving preparation as part of run. A correlated external system belongs in the same initial joint input, possibly absorbed into the arbitrary retained reference. Equal external marginals do not establish the required joint comparison.

IS.27 bounds complete-output error by terminal Kraus error plus half the largest mode loss-density error. IS.28/29 and complete-output convergence provide sufficient data for those errors. The common realized downstream action preserves these upper bounds. The existing concatenate_original supplies legal original continuation at the same base and matching current height for every finite duration including zero, with the literal prefix and relatively translated real-phase tail. Its original regularity and winding scope is unchanged; it supplies no post-failure positive-carrier restart. No omitted old programme fields, different guards or earlier quantum cuts become accessible. No relative phase waveform, real-lift anchor, calibrated phase acquisition or noisy phase unwrapping is obtained. Unknown past beta,m are not passed to the controller. An acquisition service or complete internal observer still needs its own joint legality, failure and update proof; this is an independent limitation and no construction of such a service is promised.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDownstreamOutput.downstream_distance_le`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDownstreamOutput.downstream_operational_bound`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalDownstreamOutput.output_distance`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/RecordedOutput](../Analysis/TraceClass/RecordedOutput.md)
- Dependency: [D5/S3/Quantum/Fibers/OriginalCompleteOutputStability](OriginalCompleteOutputStability.md)
