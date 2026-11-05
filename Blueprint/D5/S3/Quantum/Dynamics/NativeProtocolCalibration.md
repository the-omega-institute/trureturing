# Actual native calibration and original-event Petz consumers

## Abstract

Actual native calibration and original-event Petz consumers

**Theorem 1.1 (Actual faithful calibration and the original empty-input Petz event).**

$$(((((((((((\operatorname{Reduced}\left(\operatorname{mulVec}\left(\operatorname{Op}\left(\operatorname{sourceTree}\left(\right), \operatorname{unit}\left(\right)\right), \operatorname{omegaZero}\left(\right)\right)\right) = \operatorname{chi}\left(\right)) \land (\operatorname{calls}\left(\operatorname{sourceTree}\left(\right), \operatorname{unit}\left(\right)\right) = 3)) \land \operatorname{PosDef}\left(\operatorname{chi}\left(\right)\right)) \land (\operatorname{trace}\left(\operatorname{chi}\left(\right)\right) = 1)) \land (\operatorname{det}\left(\operatorname{chi}\left(\right)\right) = {(\operatorname{t}\left(\right))}^{4})) \land (\operatorname{cfc}\left(\operatorname{sqrt}\left(\right), \operatorname{chi}\left(\right)\right) = \operatorname{chiRoot}\left(\right))) \land (\forall v: \operatorname{FullVector}\left(\right), (\sum_{j \in \operatorname{Fin}\left(2\right)} \operatorname{Reduced}\left(\operatorname{mulVec}\left(\operatorname{projector}\left(\operatorname{readBit}\left(2\right), j\right), v\right)\right) = \operatorname{delta}\left(\operatorname{Reduced}\left(v\right)\right)))) \land (\operatorname{Reduced}\left(\operatorname{omegaZero}\left(\right)\right) = \operatorname{P0}\left(\right))) \land (\forall j: \operatorname{Fin}\left(2\right), (\operatorname{mulVec}\left(\operatorname{projector}\left(\operatorname{readBit}\left(2\right), j\right), \operatorname{omegaZero}\left(\right)\right) = \operatorname{if} (j = 0) \operatorname{then} \operatorname{omegaZero}\left(\right) \operatorname{else} 0))) \land (\operatorname{entry}\left(\operatorname{petz}\left(\operatorname{Reduced}\left(\operatorname{omegaZero}\left(\right)\right)\right), 1, 1\right) = \operatorname{complex}\left(\operatorname{emptyTarget}\left(\right)\right))) \land (\forall C: \operatorname{Function}\left(\operatorname{Fin}\left(2\right), \operatorname{Tree}\left(\operatorname{Stop}\left(\right)\right)\right), (\operatorname{eventMass}\left(\operatorname{extensionAt}\left(\operatorname{active}\left(\right), C\right), \operatorname{terminalBitOne}\left(2\right)\right) \ne \operatorname{Re}\left(\operatorname{entry}\left(\operatorname{petz}\left(\operatorname{Reduced}\left(\operatorname{omegaZero}\left(\right)\right)\right), 1, 1\right)\right) \land \frac{1}{11*({(\operatorname{kappa}\left(\right))}^{2*\operatorname{maxCalls}\left(\operatorname{extensionAt}\left(\operatorname{active}\left(\right), C\right)\right)}+\frac{13+5\sqrt{5}}{22})} \le \operatorname{abs}\left(\operatorname{eventMass}\left(\operatorname{extensionAt}\left(\operatorname{active}\left(\right), C\right), \operatorname{terminalBitOne}\left(2\right)\right)-\operatorname{Re}\left(\operatorname{entry}\left(\operatorname{petz}\left(\operatorname{Reduced}\left(\operatorname{omegaZero}\left(\right)\right)\right), 1, 1\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolCalibration.original_empty_petz_consumer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

Use the same full sixteen-bit carrier, root, fourteen addresses, selectors and stop-aware continuations defined in NativeProtocolGraft. The source tree is exactly the chronological three forward calls K3,K2,K1, ending at an active cut. The bijection cut splits shifted bit 2, the original b1, from all fifteen remaining bits. Reduced(v) is the existing partialTraceRight of the rank-one full-carrier matrix, reindexed only by this bijection. This mathematical reduction adds no physical deletion, state preparation or protection of the complement.

The actual gate action on a computational vector has its original diagonal coefficient and one possible center-flip coefficient. Applying it three times to the original root gives a squared times b at 000, a times b squared at 100, zeta times a times c at 001, zeta times b times c at 101, and zeta times b squared at 010, with all other native bits unchanged. Here a=-t, b=-beta times zeta to the fourth, c=-t times zeta cubed. The partial trace contracts equal complement words. It gives chi exactly, with entries t,gamma,conjugate gamma,t squared, where gamma=t squared times beta times conjugate of zeta to the fourth. These weights are computed from that same pure native vector.

The theorem proves that chi is positive definite, has trace one and determinant t to the fourth. Its positive square root is chiRoot=(chi+t squared I)/sqrt(1+2t squared). Positivity of the actual partial trace and uniqueness of the positive square root are reused directly. No faithfulness or square-root identity is assumed. The source tree has exactly three expanded forward calls.

For every full-carrier vector v, summing the two reduced outputs of the actual original b1 projectors gives delta(Reduced(v)), where delta(X) is the diagonal matrix with entries Xii. Each original j output remains a distinct branch; this equality is their mathematical marginal. The empty original root reduces to P0. Its actual j=0 projected vector is the same root and its j=1 vector is zero.

The fixed mathematical Petz map is petz(Y)=sqrt(chi) delta(W Y W) sqrt(chi), with W the existing continuous functional calculus of inverse square root at delta(chi). The existing diagonal functional-calculus theorem identifies W with diag(beta inverse,t inverse). Direct evaluation on the actual empty-root reduction gives petz(Reduced(Omega))11=q=(13-5sqrt(5))/22=t to the fourth divided by (1+2t squared). This is an ideal comparison value, not a native operation or an assumed input probability.

For every complete original continuation table C from the native b1 read to trees of Stop labels, let T=extensionAt(active,C). For the actual terminal event z1=1, summing all acquired paths and terminal complement words, eventMass(T,e) differs from the real part of that same Petz entry and obeys the displayed factor-eleven lower bound. The maximum is that of the complete syntactic tree, including zero, failure and stopped outcomes. The proof consumes original_event_arithmetic and original_event_resource_bounds at this actual T and event. No arbitrary event-mass surrogate, conditioning or success normalization is introduced.

This consumer establishes the three-call calibration and empty-input comparison. The original five-call prefix K3,K2,K1,K10,K13 with every X,Y archive and retained j, its ideal w value, the full identity extension on the complement and original records, failure-zero law and total-variation consumers remain open. Full V88 theorem 24.1 still requires its actual cut determinant and spectral bounds. NativeProtocolBornNormalization supplies the separate complete-tree Born law and arbitrary-position acquired-event cut trace. The semantic identity of the ninth gate power with its inverse remains unproved here. The fixed source obligations are not narrowed to this consumer.

**Theorem 1.2 (The same acquired event has its original b1 marginal and positive-mass bound).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{HistoryEvents}\left(T\right), (((\operatorname{Re}\left(\operatorname{trace}\left(\operatorname{eventReduced}\left(T, e\right)\right)\right) = \operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right)) \land \operatorname{PosSemidef}\left(\operatorname{eventReduced}\left(T, e\right)\right)) \land (0 < \operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right) \Rightarrow {(\operatorname{kappa}\left(\right))}^{-2*\operatorname{maxCalls}\left(T\right)} \le \operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolCalibration.original_event_cut_mass_and_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

For every original tree T and Boolean predicate e on its complete acquired path, eventReduced sums the actual full-carrier branch reductions over precisely those histories. The cut is the original b1 at shifted position 2, with all fifteen complementary bits retained in the mathematical partial trace. Its trace has real part equal to eventMass(T,historyEvent(e)), and its matrix is positive semidefinite. Zero events and zero branches are included.

If this raw mass is positive, the existing event resource theorem supplies the lower bound kappa to minus twice maxCalls(T). The theorem consumes the actual event trace and positivity constructions and the original arithmetic resource bound. It assumes no normalization or faithfulness of this marginal. NativeProtocolBornNormalization separately establishes unit total mass and the complex trace equality at every position cut. The cut determinant, spectral bounds and full-record reference-history Petz consumers remain open.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolCalibration.original_empty_petz_consumer`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolCalibration.original_event_cut_mass_and_psd`
- Dependency: [D5/S3/Quantum/Dynamics/NativeProtocolEventArithmetic](NativeProtocolEventArithmetic.md)
