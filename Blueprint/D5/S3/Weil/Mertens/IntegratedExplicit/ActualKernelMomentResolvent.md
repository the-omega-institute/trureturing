# Original full-kernel certificate source

## Abstract

The complete actual-K moment certificate.

**Theorem 1.1 (correlation continuous).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual real complex-prefix correlation is continuous, by the published finite shifted-hinge identity.

**Theorem 1.2 (S half window).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_half_window`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_half_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual real correlation is even by translating the complex integral and conjugating. Splitting its full resolvent convolution at zero gives one quarter of the reflected-exponential pair on [0,D]. No even spectral measure is assumed.

**Theorem 1.3 (actual fullR resolvent identity).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_resolvent_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_resolvent_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal fullR=exp(-abs(t)/2)(U(exp(abs(t)))-log(2pi)) is reconstructed from the complete finite Mangoldt sum, the exp(s/2) integral and the b(D) reflected boundary. Compact-square Fubini gives -(1/2)integral_[0,D] fullR*c=d0 W+V. The V definition retains 2 sum Lambda(n)/sqrt(n) S(log n), -2 integral exp(t/2)S(t), and -b(D)Z/2.

**Theorem 1.4 (original K split).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.original_K_split`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.original_K_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual ActualKernelLocalPositivity.K is exactly the sum of the full positive P and full arithmetic fullR by its original definition.

**Theorem 1.5 (actual fullR correlation).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The owner-local finite ramp/FTC identity is consumed to obtain Re Q_fullR=-d0 E-primeQuadratic+continuum-(1/2)integral fullR*c. Every prime power and entering upper-cutoff term remains.

**Theorem 1.6 (actual kernel moment balance).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_kernel_moment_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_kernel_moment_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This separately proved intermediate combines the actual prime row, complete positive mixture and literal resolvent identity. Its lower expression retains the unpaid continuum, d0 W and V, and its second conjunct pays W<=delta_q E/4 from the retained moment theorem. The full endpoint below proves the further continuum/cutoff payments independently; this intermediate remains a separately recorded theorem.

**Theorem 1.7 (W nonneg).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized actual W=E-Re Q_exp(1/2) is nonnegative because the retained owner now proves it equals one quarter of the finite causal-response square integral plus its endpoint square. Only zero mass is required.

**Theorem 1.8 (S abs le W).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_abs_le_W`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_abs_le_W` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual convolution S satisfies abs(S(t))<=W for every real t. Two shifted copies of the original atomic family are retained as I+I and put in [0,D+abs(t)]. Expanding their actual correlations and translating the integrals gives W(sum/difference)=2W +/- 2S(t). Nonnegative causal squares of both families yield the translated real Cauchy bound, with no spectral hypothesis or energy division.

**Theorem 1.9 (actual resolvent control).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_resolvent_control`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_resolvent_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original complex atomic moments 0,...,q, the actual S/W/Z satisfy 0<=W, every abs(S(t))<=W, W<=delta_q E/4, and abs(Z)<=4 exp(D/2)W. Positivity and shifts use actual finite causal squares; the quantitative upper payment uses the retained compiled moment theorem.

**Theorem 1.10 (correlation_neg).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

**Theorem 1.11 (W_eq_exponential_deficit).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_eq_exponential_deficit`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_eq_exponential_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

**Definition 1.12 (shiftedNodes).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shiftedNodes`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shiftedNodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

**Definition 1.13 (shiftedCoeffs).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shiftedCoeffs`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shiftedCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

**Theorem 1.14 (shifted_correlation).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shifted_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shifted_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

**Theorem 1.15 (S_even).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_even`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

**Theorem 1.16 (shifted_W).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shifted_W`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shifted_W` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Resolvent symmetry and translated-pair supplier consumed by the finite atom construction.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_abs_le_W`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_even`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_half_window`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_eq_exponential_deficit`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_nonneg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_correlation`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_resolvent_identity`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_kernel_moment_balance`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_resolvent_control`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_continuous`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_neg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.original_K_split`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shiftedCoeffs`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shiftedNodes`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shifted_W`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.shifted_correlation`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture](ActualKernelMomentMixture.md)
