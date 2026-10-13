# The complete selected endpoint moment

## Abstract

Equal-mass integral comparison supplies lower bounds for the original selected endpoint moment.

**Theorem 1.1 (A monotone cost is minimized at the left endpoint).**

Lean statement: `D5/S3/Arith/Robin/SelectedEndpointMoment.monotone_window_integral_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/SelectedEndpointMoment.monotone_window_integral_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measure mu on the real line, l<=b<=r, measurable S contained in [l,r], and f monotone on [l,r], suppose S and [l,b] have finite equal measure and f is integrable on both sets. Then integral_[l,b] f<=integral_S f. The closed lower endpoint retains atomic mass. Thresholding by f(b) compares the two indicators pointwise; equal mass cancels the constant cost.

This is the classical monotone rearrangement or bathtub principle. The proof reuses Mathlib integral_mono, integrable indicators and setIntegral_const. The equal-mass window theorem was not found as a direct supplier in the pinned Mathlib or project search.

**Theorem 1.2 (An actual moment lower bound from the endpoint secant).**

Lean statement: `D5/S3/Arith/Robin/SelectedEndpointMoment.selected_endpoint_moment_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/SelectedEndpointMoment.selected_endpoint_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the original H(t)=t^(4/5) and B(t)=t+H(t), with a>0 and every measurable selected set S contained in (0,a]. Keep the full tail T=S intersect {t:a<B(t)} and put m=volume(T), Q=integral_T ((B(t)-a)/H(a))^2. The theorem produces tau in (0,a) with B(tau)=a and proves integral_[tau,tau+m] ((B(t)-a)/H(a))^2<=Q and m^3/(3(a-tau)^2)<=Q.

Continuity and positive width supply the crossing clock. Strict monotonicity puts the actual full tail in [tau,a], so finite mass, the comparison interval and all integrability obligations are paid. The same equal-mass theorem supplies the integral comparison. Concavity of the literal B gives (t-tau)/(a-tau)<=(B(t)-a)/H(a). Exact integration of the quadratic comparison cost gives the cubic bound; the comparison interval is only a bound and does not replace or thin the original S.

The reusable statement keeps every measurable S in scope, including zero-mass tails. For the project's 5040 Robin source, instantiate a with the actual final clock and S with the complete selected domain after paying the stated support and measurability premises. This proves the two non-strict inequalities only. Equality characterization, strictness for m>0 and the square-credit transport are not declarations of this module.

The bound depends on the actual tail mass m. No fixed positive Q/M ratio follows without further mass distribution. The weighted ordinary-prime lower bound, branch and terminal bills, full Robin inequality for all n>5040 and RH remain open.

Both source-owned complete typed four-slot audit proofs compile with standard axioms. Their current scoped report nevertheless records declared_unresolved: IE-C050 unclassified_form/source.params for the general minimum and source.state_or_output for the actual moment. Neither entry is declared_validated. The exact classification gaps are disclosed in https://github.com/the-omega-institute/trureturing/issues/16350. Mathematical delivery follows the section 3.9 linked-issue exception without changing the judge or the theorems.

## References

- Truth anchor: `D5/S3/Arith/Robin/SelectedEndpointMoment.monotone_window_integral_minimum`
- Truth anchor: `D5/S3/Arith/Robin/SelectedEndpointMoment.selected_endpoint_moment_bounds`
- Dependency: [D5/S3/Arith/Robin/OriginalMovingWindowMoment](OriginalMovingWindowMoment.md)
