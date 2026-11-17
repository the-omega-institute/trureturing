# The literal residual and one threshold for all record prices

## Abstract

The complete critical residual beyond the first layer.

The complete residual beyond the first layer combines the finite higher-layer loss bound, the compact second-margin expansion, and the second-layer fixed-tube estimate. The one threshold is chosen before the original integer and its arbitrary positive record price. The complete first-layer bound remains open.

Exact target, retained without weakening: for every epsilon>0 there exists X0>1, chosen before every natural m>=2 and every real mu>0, such that if the ORIGINAL objective at mu strictly exceeds its value at EVERY natural 0<k<m and X=log(m)>=X0, then 0<=sqrt(X)*log(X)^3*(actualDefect(X,m)-completeFirstLayerLoss(X,m))<epsilon. Here referencePrice(X)=1/(X log(X)) defines the pressure clock. The original arbitrary mu is never identified with that price. No defect bound, RH, prime short-window premise, support cap, or exponent cap is an assumption.

**Theorem 1.1 (One own-X threshold before all literal records and prices).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualRecordCriticalResidual.actual_record_critical_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualRecordCriticalResidual.actual_record_critical_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every epsilon>0 the theorem chooses ONE X0>1 before every integer m>=2 and arbitrary original price mu>0 satisfying the literal strict objective comparison with EACH positive predecessor k<m. If X=log(m)>=X0, its conclusion is exactly 0<=sqrt(X)*log(X)^3*(actualDefect(X,m)-completeFirstLayerLoss(X,m)) <epsilon. The original mu is never replaced by referencePrice(X).

G1 fixes delta>0 first. tube_endpoint_limits gives separately, for each fixed s, t_X(s)->infinity, t_X(s)/sqrt(X)->sqrt(2), and log(X)/log(t_X(s))->2. theta_error_at_tube applies global theta_error_log_power(1), multiplying its normalized error by these two ratios. Thus (log(X)/sqrt(X))*(theta(t)-t)->0 at EACH endpoint s=s0-delta and s=s0+delta. fixed_tube_eventually converts their separate delta/2 tails into exactly the two finite theta inequalities. The explicit secondExpansionError tends to zero by Mathlib log-power/rpow asymptotics, while the endpoint geometry gives sqrt(X)<A. No shrinking delta(X), interval PNT premise, or assumed cancellation of errors is used.

The only new own-clock helper is appended inside FullArithmeticCorrectionSecondOrder. record_second_own_clock_limit uses the ORIGINAL unit_sqrt(unit_inv(record_mass_limits.2.2)), second_layer_limits, second_mul_unit and relative_clocks. It transports Q2/sqrt(P) to Q2/sqrt(X) and log(P) to log(X), obtaining coefficient -log(2)/sqrt(2). This helper has the actual same-delivery residual proof as its consumer. No standalone own-log module or three-conclusion wrapper is imported or retained.

G2 uses the existing record_log_envelope X<=P*log(4P^2) to prove P escape on ALL record pairs filtered by comap(X,atTop). The existing record_mass_limits supplies X/P->1; the original record_layer_ratio at j=3 supplies Q3^3/P->3. Choose R=(X*log(X)/log(2))^(1/3). The real power identities give EXACTLY X*log(X)=log(2)*R^3. Eventually X/2<=P<=2X and log(4P^2)<=4log(X). The standard limit log(X)/X^(1/4)->0 and X^(1/4)>=8 imply R,Q3<=X^(5/12). Consequently 1<=R<=sqrt(X)<X/2<=P. The finite higher bound applies without any valuation assumption at P or artificial support cap.

The COMPLETE normalized finite higher envelope is squeezed between zero and 8*log(X)^3/X^(1/12), tending to zero by the existing log-power/rpow asymptotic. Indeed 2R/P<=4X^(5/12)/X, and Q3*log(4P^2)/(X log(X))<=4X^(5/12)/X. The identity sqrt(X)*X^(5/12)*X^(1/12)=X gives the displayed normalization. This deliberately coarse envelope suffices; no reproof of the owner's rate calculus or infinite summation is involved.

G3 chooses delta=min(1,sqrt(sqrt(2)*epsilon/36)) BEFORE all thresholds, so 9delta^2/sqrt(2)<=epsilon/4. The own-X Q2 coefficient gives A<Q2<B. Intersect this tail with G1 and the complete higher-loss epsilon/2 tail. Antitone actual valuations come from price_record_prime_structure. Apply the finite second-layer theorem and combine its nonnegative loss with the complete higher loss by the exact defect split. The total is <epsilon/4+epsilon/2<epsilon. eventually_comap followed by eventually_atTop extracts one B; X0=max(B,2) precedes m and mu. There is no fixed-price or subsequence restriction.

The mathematical theorem retains the exact literal record telescope and complete loss. Its four-slot source audit remains separate: the final-law negative-family variation and sensitivity use arbitrarily large literal records, while actual observational dependence on a lawful scoped reconstruction, exact sourceSelection and current producer binding still require evidence. The existing validated compact raw-margin registration is preserved. No complete registration is asserted for this uniform residual or the newly visible owner suppliers; their unfinished audit evidence is tracked in https://github.com/the-omega-institute/trureturing/issues/28966.

An ordinary sharper estimate also follows from the same finite bound. Choose R=(X L/log(2))^(1/3). The existing same-integer record_mass_limits gives X/P->1 uniformly, and record_log_envelope gives X<=P log(4P^2), so X->infinity forces P->infinity before arbitrary prices. FixedLayerRigidity at j=3 gives Q3^3/P->3; eventually X/2<=P<=2X, Q3<=2X^(1/3), L>=2, log(4P^2)<=4L, M3<=8X^(1/3)L, R>=1 and R<P. The finite higher theorem therefore yields r L^3 D3 <= 4/(log(2)^(1/3))*X^(-1/6)*L^(10/3)+8X^(-1/6)*L^3. Both terms tend to zero by the existing log-power versus positive-real-power asymptotic. This sharper envelope counts the whole missing tail once per prime; the Pro pair-count logarithmic factor is unnecessary.

5040 application and first-layer boundary

The record theorem's conditional 5040 application uses only the existing uniform_actual_least_crossing_price_record and uniform_actual_height_escape, with Tepsilon=max(Trecord,Tescape(X0)) chosen before eta,T,m. The former gives a positive original price and the strict objective comparison with EVERY positive predecessor; the latter and divisor_log_le_log give log(m)>X0. No named binding wrapper is needed. This is conditional on being an actual least crossing and constructs none. It asserts no Robin sign or RH conclusion. First-layer boundedness sqrt(X)*log(X)^3*C1=O(1) remains explicitly OPEN after full residual isolation. Neither the finite estimates nor the ordinary Pro argument changes that boundary.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualRecordCriticalResidual.actual_record_critical_residual`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual](ActualRecordHigherLayerResidual.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
