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

**Theorem 1.9 (Explicit literal V energy obstruction).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.literal_V_energy_moment_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.literal_V_energy_moment_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number q>=1 and every D>=log(2)+1/16, an explicit family indexed by Fin(q) x Fin(3) x Bool has 6q listed atoms in [0,1/16] union [log(2),log(2)+1/16]. Put ell=1/(16q), r=exp(-ell/4), and nu=delta(0)-(1+r)delta(ell/2)+r delta(ell). The family is (I-T_log(2))(I-T_ell)^(q-1)nu. Its complex polynomial moments vanish through degree q and its positive exponential moment vanishes. Its degree q+1 moment and its x exp(x/2) moment are nonzero. The original prefix energy is strictly positive and the inclusive full Mangoldt expression satisfies V/E<=-1/(65536q^2), including q=1 and every later prime-power cutoff.

Finite differences give the exact residuals (-1)^(q+1)(q+1)! log(2) ell^q(1-r)/2 and (ell/2)(1-exp(log(2)/2))(1-exp(ell/2))^(q-1)(exp(ell/4)-1). The actual finite resolvent identity makes the three-atom response vanish outside [-ell,ell]. Translation separation scales energy and W by the same positive sum of squared binomial coefficients. The two log(2)-separated copies have energy 2N Eg and S(log(2))=-N Wg. Combining the two continuum shifts before estimating gives a bound 4h exp((log(2)+h)/2)N Wg, where h=1/16. All integer terms from 3 onward and the boundary vanish exactly. The scalar estimate Wg>=r^2 ell^3/48 supplies the stated energy constant. This is a literal-V obstruction at fixed support; it makes no full-K or RH claim and asserts no necessary dependence of moment order on D.

**Theorem 1.10 (actual resolvent control).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_resolvent_control`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_resolvent_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original complex atomic moments 0,...,q, the actual S/W/Z satisfy 0<=W, every abs(S(t))<=W, W<=delta_q E/4, and abs(Z)<=4 exp(D/2)W. Positivity and shifts use actual finite causal squares; the quantitative upper payment uses the retained compiled moment theorem.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_abs_le_W`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.S_half_window`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.W_nonneg`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_correlation`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_fullR_resolvent_identity`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_kernel_moment_balance`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.actual_resolvent_control`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.correlation_continuous`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.literal_V_energy_moment_obstruction`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentResolvent.original_K_split`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture](ActualKernelMomentMixture.md)
