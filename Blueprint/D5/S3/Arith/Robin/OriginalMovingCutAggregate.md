# The Original Moving-Cut Discrepancy

## Abstract

The actual moving-cut contribution retains its complete signed rows and original measurable selections.

A direct scalar consequence of the aggregate bound is uniform smallness relative to the original positive mass: 6 ell^(-99/500)log(2ell) tends to zero as ell tends to infinity. For each epsilon>0 choose one ell_0 before R and S; every ell>=ell_0, R>ell and complete measurable S subset [ell,R] with M=volume(S)>0 then satisfy |C_cut(S)+P_cut(S)|<=epsilon M. This is an ordinary limit consequence of the exact compiled bound; no separate Lean limit theorem is claimed. It pays the cut remainder only, and gives no bound on either summand alone, the other paired/early baseline, or the total ordinary-prime signed contribution.

These original proofs reuse OriginalMovingWindowMoment and the native ratio/variation suppliers in OriginalMovingCutRow. Source-owner four-slot audit is unfinished: exact actual/rejected law, bridge and whole-family variation/sensitivity compile, but qualifying actual observational-dependence witnesses and lawful sourceSelection/current binding remain missing. No validated registration is claimed; the concrete gap is tracked at https://github.com/the-omega-institute/trureturing/issues/15968.

**Theorem 1.1 (The native cut identity on a complete measurable selection).**

Lean statement: `D5/S3/Arith/Robin/OriginalMovingCutAggregate.original_cut_aggregate_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalMovingCutAggregate.original_cut_aggregate_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 256<=ell<R, let S be any measurable subset of J=[ell,R], and retain M=volume(S)>0. Set N=floor(2R). The original C_cut(S) integrates over S the full sum on positive integer pairs of mu(d)log(m)k(t,dm)(1_{t<d^(500/151)} -r_d(dm)). The actual kernel makes every term with dm>N zero. Thus its exact finite form uses 1<=d<=N and 1<=m<=N/d, where N/d is natural-number division. These are exactly all positive integer pairs with dm<=N.

Define P_t(x)=sum over 1<=d<=floor(t^(151/500)) of mu(d)log(x/d)/d and Pbar(x)=integral_J k(s,x)P_s(x) ds divided by K_J(x), with the real zero convention. The original P_cut(S) is integral_S integral_t^B(t) k(t,x)(P_t(x)-Pbar(x)) dx dt. The exact floor identity d<=floor(t^(151/500)) iff t>=d^(500/151) preserves all equality endpoints. On the weighted support, k(t,x)(P_t(x)-Pbar(x))=-sum over 1<=d<=N of mu(d)F_(t,d)(x)/d. If K_J(x)=0, k(t,x)=0 for t in J, so this equality still holds.

The kernel is jointly measurable in (t,x); its parameter integrals K_J and N_d and their zero-safe ratio are measurable. On t in J each row is bounded in absolute value by log(2R)+log(d), with support inside [0,2R]. This proves the actual integrability needed for the finite sum and integral exchanges. Moving-window integrals equal fixed-support integrals because the literal kernel vanishes at both endpoints and outside each window.

The resulting identity is C_cut(S)+P_cut(S)=integral_S sum over 1<=d<=N of mu(d)latticeRowRemainder(ell,R,t,d) dt. Every row past floor(B(t)^(151/500)) is exactly zero. Therefore the complete pointwise budget gives |C_cut+P_cut|<=6 integral_S t^(-99/500)log(2t) dt <=6 M ell^(-99/500)log(2ell). The last step follows from the nonpositive derivative of the actual log-power envelope for all t>=256. The estimate depends on neither R nor the number or placement of components of S.

The kernel, complete original selections, higher prime-power reference layers and two distinct costs retain the conventions of EL Definitions 1.1-1.2 and EL Assumption 1.3 in FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_SELECTED_EULER_LAYERS. The cut identity controls this signed remainder; it gives no favorable paired baseline, early cancellation or cofinal original positive-mass witnesses. The identity identifying the complete original I_X with its paired, early and strip terms remains outside this theorem, as do the stationary FIB and Riemannian-manifold realization bridges. The full all-integer Robin/RH obligation remains open.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalMovingCutAggregate.original_cut_aggregate_estimate`
- Dependency: [D5/S3/Arith/Robin/OriginalMovingCutBudget](OriginalMovingCutBudget.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMovingCutRow](OriginalMovingCutRow.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMovingWindowMoment](OriginalMovingWindowMoment.md)
