# The Original Moving-Cut Row Suppliers

## Abstract

Literal compensated Robin rows have a source-specific bounded-variation supplier.

A direct scalar consequence of the aggregate bound is uniform smallness relative to the original positive mass: 6 ell^(-99/500)log(2ell) tends to zero as ell tends to infinity. For each epsilon>0 choose one ell_0 before R and S; every ell>=ell_0, R>ell and complete measurable S subset [ell,R] with M=volume(S)>0 then satisfy |C_cut(S)+P_cut(S)|<=epsilon M. This is an ordinary limit consequence of the exact compiled bound; no separate Lean limit theorem is claimed. It pays the cut remainder only, and gives no bound on either summand alone, the other paired/early baseline, or the total ordinary-prime signed contribution.

**Definition 1.1 (The literal continuum-compensated row).**

Lean statement: `D5/S3/Arith/Robin/OriginalMovingCutRow.cutRow`

*Formalization.* `D5/S3/Arith/Robin/OriginalMovingCutRow.cutRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the original reciprocal-log price kernel with strict lower and weak upper support, width t^(4/5), endpoint B=t+width, and lower right-limit height b=(lambda(t)-lambda(B))/(w(t)t^(11/10)). For J=[ell,R], K_J is the complete window mass and N_d is its portion before the strict divisor activation clock d^(500/151); r_d=N_d/K_J uses the real zero convention. The actual row is log(x/d)k(t,x)(1_{t<d^(500/151)}-r_d(x)).

Cross multiplication and actual integral comparisons prove the ratio decreases on positive mass. A decreasing local extension agrees after multiplication by the literal kernel at all support and equality endpoints. The logarithmic body has lower-end jump and variation at most 2 b(t)log(2t); ratio compensation adds at most b(t)log(2t). A general lattice-cell comparison pays the full grid. These private proved suppliers are consumed directly by OriginalMovingCutBudget, which states the public row and complete crossing bounds; OriginalMovingCutAggregate retains every component of the measurable selection. No private helper is copied or replaced by a theorem wrapper.

The original kernel follows EL Definition 1.2 in FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_SELECTED_EULER_LAYERS. This supplier alone concludes no favorable paired main contribution, original I_X decomposition, cofinal positive-mass witnesses, or full Robin/RH theorem.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalMovingCutRow.cutRow`
- Dependency: [D5/S3/Arith/Robin/OriginalMovingWindowMoment](OriginalMovingWindowMoment.md)
