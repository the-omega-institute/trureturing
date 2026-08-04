# Zero Geometry Beneath Weil Positivity

## Abstract

Projected zero cancellation, mirror pairing, and local balance delimit the open O-6 bridge.

<a id="describe-projected-zero-does-not-erase-the-labeled-vector"></a>

**Theorem 1.1 (A projected zero does not erase the labeled vector).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall \rho\in\mathbb{C},\ \operatorname{classicalZeta}(\rho)=0 \Rightarrow \operatorname{classicalZeta}(\rho)=0 \land \operatorname{labeledZeta}(\ell,\rho)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ZeroGeometry.projection_zero_labeled_vector_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplied classical zeta zero is retained alongside nonvanishing of its labeled coefficient function for every additive ledger. The scalar zero is an explicit hypothesis, so the declaration proves no zero exists. No analytic projection operator is defined, and no projection identity outside the Dirichlet convergence half-plane is claimed. On the O-6 path, this prevents cancellation in zeroSum from being mistaken for vacuous disappearance of the labeled data.

<a id="describe-positive-length-entries-detect-off-line-displacement"></a>

**Theorem 1.2 (Positive-length entries detect off-line displacement).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall s\in\mathbb{C},\ \forall a\in A,\ 0<\ell(a) \Rightarrow \operatorname{scalingLedger}(\ell,s,a)=(\Re(s)-\operatorname{criticalAbscissa})\ell(a) \land (\operatorname{scalingLedger}(\ell,s,a)\neq 0 \Leftrightarrow \Re(s)\neq\operatorname{criticalAbscissa}) \land (0<\operatorname{scalingLedger}(\ell,s,a) \Leftrightarrow \operatorname{criticalAbscissa}<\Re(s)) \land (\operatorname{scalingLedger}(\ell,s,a)<0 \Leftrightarrow \Re(s)<\operatorname{criticalAbscissa})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ZeroGeometry.off_line_scaling_entry_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive-length coordinate, the scaling entry is displacement from real part one half times ledger length. It is nonzero exactly off the critical line, positive to the right, and negative to the left. The explicit positivity hypothesis replaces the source ledger's concrete nonzero-address fact and strengthens the sign assertions to equivalences. The source's coefficient factorization, unbounded-ray clause, and rotation-invariance clause are not formalized here. This entry is the local quantity that an eventual O-6 positivity-to-balance argument must force to zero.

<a id="describe-a-global-factor-cannot-clear-off-line-scaling"></a>

**Theorem 1.3 (A global factor cannot clear off-line scaling).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ (\exists a,\ell(a)\neq 0) \Rightarrow \forall s,c\in\mathbb{C},\ (\forall a,\ \Vert c\operatorname{halfDensityReading}(\ell,s,a)\Vert=1) \Rightarrow \Re(s)=\operatorname{criticalAbscissa}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ZeroGeometry.global_factor_clearing_forces_critical_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nontrivial additive ledger, if one complex factor makes every half-density reading have norm one, then the parameter has real part one half. The factor is arbitrary and independent of the coordinate; exact unit norm at every coordinate is the calibrated premise. The governance claim excluding an address-dependent inverse register is not part of this theorem. Thus O-6 positivity cannot be replaced by a single global normalization shortcut.

<a id="describe-zero-data-symmetries-form-the-mirror-quartet"></a>

**Theorem 1.4 (ZeroData symmetries form the mirror quartet).**

$$\forall Z:\operatorname{ZeroData},\ \forall n\in\mathbb{N},\ \forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ Z_{C(n)}=\overline{Z_{n}} \land Z_{R(n)}=1-Z_{n} \land Z_{C(R(n))}=\operatorname{mirror}(Z_{n}) \land (\forall a,\ \operatorname{scalingLedger}(\ell,Z_{C(R(n))},a)=-\operatorname{scalingLedger}(\ell,Z_{n},a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ZeroGeometry.zero_quartet_scaling_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration is conditional on a supplied ZeroData value. Its zero_conjugation and zero_reflection fields are premises carrying the first two displayed equalities, rather than conclusions derived from real coefficients, analytic continuation, or a functional equation. ZeroData also requires a duplicate-free exhaustive enumeration of all classical nontrivial zeta zeros, exact multiplicities, reflection and conjugation permutations, their multiplicity-preservation laws, and local finiteness. The repository does not prove that ZeroData is inhabited: no instance or example exists. Accordingly this conditional declaration does not close the source theorem; that source obligation remains open. From the supplied fields Lean derives only the composed mirror equality and its algebraic reversal of every scaling entry. It proves neither pairwise distinctness nor the source's nonmultiplicative numerical instrument, and the conditional cancellation alone supplies no positivity.

<a id="describe-mirror-partners-cancel-across-distinct-positions"></a>

**Theorem 1.5 (Mirror partners cancel across distinct positions).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall s\in\mathbb{C},\ (s\neq\operatorname{mirror}(s) \Leftrightarrow \Re(s)\neq\operatorname{criticalAbscissa}) \land (\forall a,\ \operatorname{scalingLedger}(\ell,s,a)+\operatorname{scalingLedger}(\ell,\operatorname{mirror}(s),a)=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ZeroGeometry.mirror_pair_distinct_iff_off_line_and_cancels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A parameter differs from its conjugate reflection exactly when it is off the critical line, yet their scaling entries sum to zero at every coordinate. This is generalized from the concrete prime-log ledger to every additive ledger. Cross-position cancellation does not imply local balance at either position. It isolates why the convolution-square positivity quantified by O-6 must add information beyond zero-set symmetry.

<a id="describe-ontological-zero-records-projection-balance-and-closure"></a>

**Definition 1.6 (An ontological zero records projection, balance, and closure).**

Lean statement: `D5/S3/Zeros/ZeroGeometry.IsOntologicalZero`

*Formalization.* `D5/S3/Zeros/ZeroGeometry.IsOntologicalZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate conjoins a classical zeta zero, vanishing of every local scaling entry, and a carried closure-level condition. The projection clause is represented by classicalZeta rather than a separately defined analytic projection. The closure condition is carried as the arbitrary predicate closedAt; no inhabitant is asserted. This names the local-balance target for the open implication beneath O-6 without assuming it.

<a id="describe-ontological-local-balance-forces-the-critical-line"></a>

**Theorem 1.7 (Ontological local balance forces the critical line).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ (\exists a,\ell(a)\neq 0) \Rightarrow \forall \mathrm{closedAt}:\mathbb{C}\to\operatorname{Prop},\ \forall \rho\in\mathbb{C},\ \operatorname{IsOntologicalZero}(\ell,\mathrm{closedAt},\rho) \Rightarrow \Re(\rho)=\operatorname{criticalAbscissa}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ZeroGeometry.ontological_zero_re_eq_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given one nonzero ledger-length coordinate, the local-balance conjunct of an ontological zero forces its real part to one half. The abstract witness replaces the source's concrete log-two coordinate, and no property of the carried closure predicate is used. The missing implication from every projected zero to local balance is exactly the open O-6 bridge. This theorem closes only the final algebraic edge after that bridge.

## References

- Truth anchor: `D5/S3/Zeros/ZeroGeometry.IsOntologicalZero`
- Truth anchor: `D5/S3/Zeros/ZeroGeometry.global_factor_clearing_forces_critical_line`
- Truth anchor: `D5/S3/Zeros/ZeroGeometry.mirror_pair_distinct_iff_off_line_and_cancels`
- Truth anchor: `D5/S3/Zeros/ZeroGeometry.off_line_scaling_entry_spec`
- Truth anchor: `D5/S3/Zeros/ZeroGeometry.ontological_zero_re_eq_critical`
- Truth anchor: `D5/S3/Zeros/ZeroGeometry.projection_zero_labeled_vector_spec`
- Truth anchor: `D5/S3/Zeros/ZeroGeometry.zero_quartet_scaling_spec`
