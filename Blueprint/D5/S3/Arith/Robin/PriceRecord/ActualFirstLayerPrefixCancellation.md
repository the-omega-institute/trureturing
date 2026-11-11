# D5 source compiled; RegUNVALIDATED

## Abstract

Finite complete first-layer cancellation and actual-record budget comparison.

These anchors describe a D5 source target with a current scoped Lean build. Its retained Reg source compiles; the escape audit remains incomplete for lawful enrollment, source binding and variation. The loss, raw margin, optimizer layer count and unrestricted actual defect are reused from the canonical library. The companion patch only exposes original consumed helpers. No second loss, margin, optimizer or root definition is introduced. The mathematical mechanism is elementary; no literature novelty is claimed.

**Theorem 1.1 (Cancel the optimizer term on the complete common support).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Statement: X>4, arbitrary natural m,k with m.primeFactors=primesLE(P), k.primeFactors=primesLE(Q), and the real casts of P,Q,r lie in [X/2,2X]. The root equation is the existing firstLayerPrice(r)=referencePrice(X), equivalently log(1+1/r)-log(r)/(X log(X))=0 on this interval. Then |C1(X,k)-C1(X,m)| <= 6 max(|P-r|,|Q-r|) |theta(P)-theta(Q)| / (X^2 log(X/2)). Here C1 is exactly ActualRecordHigherLayerResidual.completeFirstLayerLoss.

Each complete sum extends to lossPrimes(X,m) union lossPrimes(X,k). An original helper puts every positive first margin in optimizer support, so every added coordinate has exactly zero loss. Exact prime-factor prefixes turn first occupancy into p<=P or p<=Q. The identical max(rawMargin,0) terms cancel coordinate by coordinate. If P<=Q, the oriented difference is exactly minus the raw-margin sum over the existing block(P,Q)=(P,Q] primes. The reverse ordering swaps the two original integers.

The candidate differentiates the literal real function g(t)=log(1+1/t) -log(t)/(X log(X)), obtaining g'(t)=-1/(t(t+1))-1/(X log(X)t). For every t in [X/2,2X], X>4 gives log(X)>1, the two positive derivative magnitudes are <=4/X^2 and <=2/X^2, and therefore |g'(t)|<=6/X^2. Mathlib's convex-set mean value inequality, applied to the actual root, bounds each discrepancy margin by (6/X^2) max(|P-r|,|Q-r|). The exact block log sum is theta(Q)-theta(P). Since every block prime has log(p)>=log(X/2)>0, its cardinality is at most this mass/log(X/2). No division by the mass or cardinality occurs. Equal prefixes, zero theta mass, inclusive upper endpoints and a prime root with zero margin are covered.

**Theorem 1.2 (Consume cancellation for the same original record).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Candidate statement: retain all preceding prefix/root/tube hypotheses. The ORIGINAL m is a strict record of goldenResourceObjective(mu,.) against every positive predecessor, for an arbitrary mu>0; X=log(m)>4. The integer k>=2 satisfies the concrete budget log(k)+delta=X with delta>=0. For every prime p and j>=2, j<=v_p(k) iff j<=optimalLayerCount(referencePrice(X),p). Then the actual residual R=actualDefect(X,m)-C1(X,m) satisfies 0<=R and R<=6 max(|P-r|,|Q-r|)|theta(P)-theta(Q)|/(X^2 log(X/2)) +delta/(X log(X)). The conclusion concerns m itself.

The budget proves k<=m by strict monotonicity of log. If k<m the original record comparison applies; if k=m reflexivity applies. Expanding the actual objective and using mu*delta>=0 gives D(X,m)<=D(X,k)+delta/(X log(X)). The higher-occupancy equivalence is a premise about the existing canonical optimizer counts, not a defect or loss bound. The original margin_active_iff makes every j>=2 loss of k exactly zero, including ties. The exposed original actual_defect_decomposition therefore gives D(X,k)=C1(X,k). For m the same decomposition and nonnegative coordinate losses give R>=0. Subtract C1(X,m), bound the oriented first-layer difference by its absolute value, and consume the first theorem. This is a finite result only. Comparator construction, global theta estimates, RH implications and any A2-scale limit are absent.

**Theorem 1.3 (ordered_prefix_difference).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.ordered_prefix_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.ordered_prefix_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem ordered_prefix_difference {X : ℝ} (hX : 1 < X)     {m k P Q : ℕ} (hmprefix : m.primeFactors = Nat.primesLE P)     (hkprefix : k.primeFactors = Nat.primesLE Q) (hPQ : P ≤ Q) :     completeFirstLayerLoss X k - completeFirstLayerLoss X m =       -(∑ p ∈ block (P : ℝ) Q, rawLayerMargin X p 1)

**Theorem 1.4 (raw_first_bound_at_root).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.raw_first_bound_at_root`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.raw_first_bound_at_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem raw_first_bound_at_root {X r t : ℝ} (hX : 4 < X)     (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     (ht : t ∈ Set.Icc (X / 2) (2 * X)) :     |log (1 + 1 / t) - log t / (X * log X)| ≤ (6 / X ^ 2) * |t - r|

**Theorem 1.5 (defect_eq_first_of_optimizer_higher_layers).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.defect_eq_first_of_optimizer_higher_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.defect_eq_first_of_optimizer_higher_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete statement: theorem defect_eq_first_of_optimizer_higher_layers {X : ℝ} (hX : 1 < X) {k : ℕ} (hk : 1 ≤ k) (hhigher : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j → (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p)) : actualDefect X k = completeFirstLayerLoss X k

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.defect_eq_first_of_optimizer_higher_layers`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.ordered_prefix_difference`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.raw_first_bound_at_root`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualBalancedCutoff](ActualBalancedCutoff.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity](ActualFirstLayerBlockCoercivity.md)
