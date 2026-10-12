# The Original Moving-Window Moment

## Abstract

An explicit uniform error controls the continuous decaying moment of the original Robin moving-window kernel.

Use lambda(x)=1/(x log(x)) and the existing weight w(x)=(log(x)+1)/(x^2 log(x)^2). The original window has H(t)=t^(4/5), B(t)=t+H(t) and kernel k(t,x)=(lambda(x)-lambda(B(t)))/(w(t)*t^(11/10)) for t<x<=B(t), and zero elsewhere. In particular k(t,t)=0 and k(t,B(t))=0. The price is evaluated only inside the legal window; real powers are Real.rpow.

**Theorem 1.1 (A quantitative continuous moment supplier).**

Lean statement: `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_window_moment_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_window_moment_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t>=4 and beta>=0, define a_beta(t)=integral from t to B(t) of k(t,x)*(x-2)^(-beta). With C_beta=4+beta+2*beta*2^(beta+1), |a_beta(t)-t^(1/2-beta)/2| <= C_beta*t^(-1/5)*t^(1/2-beta)/2.

The proof reuses ActualRobinClockCovariance.g, its original derivative and density-integral suppliers, and MellinWeightedVariation.scaleWeight_antitone. Their weight normalization gives w(B)*(B-x)<=lambda(x)-lambda(B)<=w(t)*(B-x). The logarithmic growth estimate proves (t/B)^4*w(t)<=w(B). Exact integration of these bounds gives the endpoint moment bounds (t/B)^4*(B-2)^(-beta)*H^2/(2*t^(11/10)) <=a_beta(t)<=(t-2)^(-beta)*H^2/(2*t^(11/10)). Negative-power derivative estimates and H^2/t^(11/10)=sqrt(t) supply the displayed error. A triangle enters only as a proved bound on the same price-difference kernel.

The source definition is EL Definition 1.2 in FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_SELECTED_EULER_LAYERS. The estimate applies separately to every point of any complete original S_X contained in [4,infinity), for example when ell_X>=4; it does not select, thin or displace that family. At beta=1/2 its continuous single-window main term is 1/2.

This is a continuous kernel supplier. It proves no integral interchange for W_X, no absolute lattice error and no discrete critical-threshold theorem. It does not identify a geometric trajectory with the original maximizing integers or prove their cofinal existence. The initialized seven-divisibility guard has mean p_0+p_25, including Q=0; its testing error is not Lambda-1 or I_X. The proposed calibration s=x-3, mass-action flow, entropy and Fisher-action claims remain outside this theorem. The full signed Robin/RH obligation remains open.

**Theorem 1.2 (A moving-cut row with its continuum compensation).**

Lean statement: `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_cut_row_lattice_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_cut_row_lattice_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 256<=ell<R, J=[ell,R], t in J and d>=1 be an integer. Use the same literal kernel, K_J(x)=integral_J k(s,x) ds, N_d(x)=integral_(J intersect {s<d^(500/151)}) k(s,x) ds and r_d(x)=N_d(x)/K_J(x), with zero ratio at zero mass. Write F_(t,d)(x)=log(x/d)k(t,x) (1_{t<d^(500/151)}-r_d(x)) and b(t)=(lambda(t)-lambda(B(t)))/(w(t)t^(11/10)).

The complete row remainder is the sum over 1<=m<=floor(2R)/d of log(m)k(t,dm) (1_{t<d^(500/151)}-r_d(dm)), minus (1/d)integral_t^B(t) F_(t,d)(x) dx. Its absolute value is at most 3 b(t) log(2t). The height satisfies 0<=b(t)<=t^(-3/10). The sum includes the zero log at m=1, every nonzero Mobius row remains available for subsequent signed summation, and the floor is applied before the natural-number division.

Cross multiplication of the literal kernels and two integral comparisons show that r_d decreases wherever K_J is positive. Positivity of k(t,x) for t in J implies positivity of K_J(x), including the ends of J. The ratio's zero extension need not decrease. On a single window use the decreasing extension taking value 1 on x<=t and 0 on x>=B(t); multiplication by k(t,x) agrees exactly with the original ratio at all x, including both zero endpoints.

For d<=B(t)^(151/500), the logarithmic price body decreases on [t,B(t)]. Its zero extension has the lower-end jump and variation at most 2 b(t)log(2t). The decreasing ratio adds at most b(t)log(2t). For d>=B(t)^(151/500) the original row is zero, since all its positive reference mass precedes the divisor clock. Variation on adjacent lattice cells adds to variation on the full grid. The initial zero cell and the entire last cell are included; the last grid endpoint exceeds 2R.

This row estimate supplies no count of crossing integer rows and no summed bound with exponent -99/500. Integral interchange over an arbitrary complete selected S, the favorable paired term, the early-error estimate and cofinal positive-mass original witnesses are not conclusions of this theorem. The full signed Robin/RH obligation remains open.

**Theorem 1.3 (The complete pointwise crossing budget).**

Lean statement: `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_cut_row_pointwise_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_cut_row_pointwise_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 256<=ell<R and t in [ell,R], sum the actual signed-row magnitudes over every integer 1<=d<=floor(B(t)^(151/500)). Rows with d<=floor((t-t^(4/5))^(151/500)) vanish from the literal strict-left cutoff, including zero-normalizer and endpoint cases. The remaining interval has at most 2*t^(51/500) integer labels.

Applying the source-specific row estimate and |mu(d)|<=1, then b(t)<=t^(-3/10), gives the complete bound sum_d |mu(d)|*|latticeRowRemainder(ell,R,t,d)| <= 6*t^(-99/500)*log(2t). The original divisor rows remain available with their signed Mobius factors for later aggregation; absolute values pay only this pointwise budget.

This is the exact crossing-count bridge before integration over a measurable complete S. It does not prove the finite-Fubini identity for C_cut+P_cut, the arbitrary-S integral estimate, the paired baseline inequality, early-error decay, cofinal witnesses, or the full signed Robin/RH conclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_cut_row_lattice_estimate`
- Truth anchor: `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_cut_row_pointwise_budget`
- Truth anchor: `D5/S3/Arith/Robin/OriginalMovingWindowMoment.original_window_moment_estimate`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
