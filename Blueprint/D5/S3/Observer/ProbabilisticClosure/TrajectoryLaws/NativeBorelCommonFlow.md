# Full laws and the acquired return

## Abstract

Acquired common flows on full legal-tail probability descriptors.

ValidTail(p) consists of every complete word pWord(n,i) and the infinite noncompletion outcome. ValidTail(beta) consists of betaStop, every alpha-prefixed pWord(n,i), and noncompletion. These are the legal full-tail carriers of NativeFullResidual, whose renderer retains original operation blocks and complete-law total variation. The source samples one positive depth in {1,2,3}, with rates 1/3, 2/5 and 3/8, before any paid Read; the analysis below introduces no observer registers.

RegularDescriptor(s) is a probability law on ValidTail(s), with emission in [1/3,2/5] and every source tail inequality at rate 4/15. The suspended tail has the additional factor 2/5. Its measurable structure is inherited from the Giry evaluation structure. Equality of this structure with complete-law-TV Borel is not asserted by the statements here.

CommonFlow contains the original probability measures GammaB and GammaA, their four common unweighted margins nuP and nuB, and the same exhibited Markov disintegrations B and A. Both complete-atom endpoint boxes are included, including noncompletion. The residual contract equates (1-u(Q)) inverse times the prefix-deleted input law to the full B barycenter, and v(W) inverse times the prefix-deleted input law to the full A barycenter. The legal-word partitions then reconstruct the input measure: law(Q)=u(Q) delta_alpha+(1-u(Q)) map(prependB,barycenter(B(Q))); law(W)=(1-v(W)) delta_beta+v(W) map(prependA,barycenter(A(W))). Barycenters are full opposite laws, without opposite regularity requirements. prependB and prependA restore the deleted original letter and preserve noncompletion.

C is A composed after B. L weights the A row by v(W) and the resulting B composition by 1-u(Q). Thus its action is (Lf)(Q)=(1-u(Q)) integral v(W) integral f(Qprime) A(W,dQprime) B(Q,dW). iterate(L,f,0)=f and iterate(L,f,n+1) is integration of iterate(L,f,n) against the L row. coordinate(n,i,Q) is Q{pWord(n,i)} and g(Q)=coordinate(0,1,Q). AE(mu,Q,P) denotes P for mu-almost every Q; BIntegral(F,Q,oneMinusV) denotes the integral of 1-v under the original B row. measureComp, row and smul denote measure composition, kernel evaluation and nonnegative measure scaling.

**Theorem 1.1 (Both entire word families).**

$$\forall F: CommonFlow, (\operatorname{measureComp}\left(\operatorname{C}\left(F\right), \operatorname{nuP}\left(F\right)\right)=\operatorname{nuP}\left(F\right))\land((\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \forall n: Nat, \forall i: Letter, \operatorname{coordinate}\left(n, i, Q\right)=\operatorname{iterate}\left(\operatorname{L}\left(F\right), \operatorname{coordinate}\left(0, i\right), n, Q\right)\right))\land(\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{g}\left(Q\right)=(1-\operatorname{u}\left(Q\right)) \cdot \operatorname{BIntegral}\left(F, Q, \operatorname{oneMinusV}\left(\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_word_iteration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The disintegrations and common margins make nuP stationary for C. Evaluating the two full residual identities at each complete word gives the one-return recurrence. L is dominated by C, so stationarity transports the null exceptions through every iterate. Countable conjunction yields one full-measure set for every index and bit. At the first marker-one word, reconstruction gives the completion integral.

**Theorem 1.2 (Uniform row bounds and the upper three-return box).**

$$\forall F: CommonFlow, (\forall Q: PDescriptor, (\operatorname{smul}\left(\frac{1}{5}, \operatorname{row}\left(\operatorname{C}\left(F\right), Q\right)\right)\leq\operatorname{row}\left(\operatorname{L}\left(F\right), Q\right))\land(\operatorname{row}\left(\operatorname{L}\left(F\right), Q\right)\leq\operatorname{smul}\left(\frac{4}{15}, \operatorname{row}\left(\operatorname{C}\left(F\right), Q\right)\right)))\land(\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\frac{9}{25}\leq\operatorname{g}\left(Q\right))\land((\operatorname{g}\left(Q\right)\leq\frac{4}{9})\land(\operatorname{iterate}\left(\operatorname{L}\left(F\right), g, 3, Q\right)\leq\frac{9}{25} \cdot {\frac{6}{25}}^{3}))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_operator_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Emission bounds place 1-u in [3/5,2/3] and v in [1/3,2/5]. Positivity of the acquired integrals gives the two measure inequalities and completion bounds. The original endpoint word masses from FourthSegmentStoppedLaw give c_a z_a^3 below c_b z_b^3, with c_b=9/25 and z_b=6/25. The full p box therefore bounds the third L iterate of g. These are conditional integrals; no assertion bounds individual sampled path products.

**Theorem 1.3 (A closed conull realization).**

$$\forall F: CommonFlow, \exists P: PSet, \exists S: BSet, (\operatorname{MeasurableSet}\left(P\right))\land((\operatorname{MeasurableSet}\left(S\right))\land((\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{Member}\left(Q, P\right)\right))\land((\operatorname{AE}\left(\operatorname{nuB}\left(F\right), W, \operatorname{Member}\left(W, S\right)\right))\land((\forall Q: PDescriptor, (\operatorname{Member}\left(Q, P\right))\Rightarrow((\operatorname{goodP}\left(F, Q\right))\land(\operatorname{AE}\left(\operatorname{BRow}\left(F, Q\right), W, \operatorname{Member}\left(W, S\right)\right))))\land(\forall W: BDescriptor, (\operatorname{Member}\left(W, S\right))\Rightarrow((\operatorname{goodB}\left(F, W\right))\land(\operatorname{AE}\left(\operatorname{ARow}\left(F, W\right), Q, \operatorname{Member}\left(Q, P\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_conull_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PSet is Set(PDescriptor) and BSet is Set(BDescriptor); Member is set membership, and BRow and ARow are the original acquired kernel rows. The predicate goodP(F,Q) conjoins the full normalized B residual equality, the full p endpoint box, both entire coordinate iteration formulas, the completion integral, 9/25 <= g <= 4/9, and iterate(L,g,3,Q) <= (9/25)(6/25)^3. The predicate goodB(F,W) conjoins the full normalized A residual equality and the full suspended endpoint box. The measurable sets P and S have full nuP and nuB measure and satisfy these predicates pointwise. Every Q in P has B(Q)-almost every successor in S, and every W in S has A(W)-almost every successor in P. Starting from measurable hulls of the null exceptions, successive sets exclude positive-probability predecessors. The two unweighted margin identities keep every exclusion null. Their countable intersections are closed under both original kernels; no transition-closure hypothesis is imposed.

**Theorem 1.4 (Normalized third return bound).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{normalizedIterate}\left(F, g, 3, Q\right)\leq\frac{9}{25}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_normalized_third_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

normalizedIterate(F,f,n,Q) is endpointRate⁻¹ raised to n times iterate(L,f,n,Q). The theorem transports the full p endpoint-box inequality at depth three through the exact scalar normalization endpointRate=6/25; it retains the original arbitrary Borel descriptor and acquired L operator.

**Theorem 1.5 (Three-step defect is nonnegative).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, 0\leq\operatorname{threeStepDefect}\left(F, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_three_step_defect_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

threeStepDefect is the truncated ENNReal difference (g−normalizedIterate(L,g,3))/3. Its nonnegativity is recorded on the same full-measure endpoint-box core; it is the finite-block input for the later Jensen/localization construction. No harmonicity, survivor event, or limit is asserted here.

**Theorem 1.6 (Normalized action advances one return).**

$$\forall F: CommonFlow, \forall f: PDescriptorFunction, \forall n: Nat, \forall Q: PDescriptor, (\operatorname{Measurable}\left(f\right))\Rightarrow(\operatorname{normalizedIterate}\left(F, f, n+1, Q\right)=\operatorname{normalizedAction}\left(F, \operatorname{normalizedIterate}\left(F, f, n\right), Q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.normalizedIterate_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar endpoint normalization commutes with one L integration. The measurable iterate witness is discharged from the same Borel kernel, and no new state or transition is introduced.

**Theorem 1.7 (Normalized action preserves nonnegative addition).**

$$\forall F: CommonFlow, \forall f1: PDescriptorFunction, \forall f2: PDescriptorFunction, \forall Q: PDescriptor, (\operatorname{Measurable}\left(f1\right))\Rightarrow(\operatorname{normalizedAction}\left(F, f1+f2, Q\right)=\operatorname{normalizedAction}\left(F, f1, Q\right)+\operatorname{normalizedAction}\left(F, f2, Q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.normalizedAction_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel integration and endpoint scaling preserve addition for the measurable first summand. This is the linearity input needed when the finite-block average is expanded; it does not assert a Jensen or localization conclusion.

**Theorem 1.8 (Normalized action of the finite-block average).**

$$\forall F: CommonFlow, \forall Q: PDescriptor, \operatorname{normalizedAction}\left(F, \operatorname{threeStepAverage}\left(F, Q\right), Q\right)=\frac{\operatorname{normalizedIterate}\left(F, g, 1, Q\right) + \operatorname{normalizedIterate}\left(F, g, 2, Q\right) + \operatorname{normalizedIterate}\left(F, g, 3, Q\right)}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.normalizedAction_threeStepAverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The acquired normalized action sends the three-step average to the corresponding three successive normalized iterates. This is an exact finite algebraic bridge for the later localization argument; no fixed point, killing, or limit is claimed.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_conull_core`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_normalized_third_step`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_operator_bounds`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_three_step_defect_nonneg`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.common_flow_word_iteration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.normalizedAction_add`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.normalizedAction_threeStepAverage`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow.normalizedIterate_succ`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual](NativeFullResidual.md)
