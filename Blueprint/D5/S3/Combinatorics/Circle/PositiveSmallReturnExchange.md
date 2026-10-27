# Physical exchange by constructive positive SMALL returns

## Abstract

Construct an actual short-positive SMALL return batch from a computable filter mass condition, retain the entire remaining SMALL batch, and strictly lower unused LARGE count.

The selected physical labels, their complementary batch and every new gate are outputs. The source is actualSource on Fin k with arbitrary natural t and k>=3; no path start p, crossing a, successor relation or global minimizer is needed.

**Theorem 1.1 (Full exchange from the actual eligible mass).**

Lean statement: `D5/S3/Combinatorics/Circle/PositiveSmallReturnExchange.actualSource_positiveSmall_return_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PositiveSmallReturnExchange.actualSource_positiveSmall_return_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s=actualSource(k,t), C=(2^k-1)/2, Q=2^(k-2). The original W=F++[zpen]++T++[z]++E0++E1 is Legal, every label of T++E0++E1 is SMALL, and n,q are unused in ALL W. Write s(n)=-D, s(zpen)=-ZZ, s(q)=qq and s(z)=-Z. The hypotheses give negative LARGE n, s(zpen)<s(n)<0, positive LARGE q, negative LARGE z and Z<=qq. Native bounds imply Q<=D<ZZ<=C and Q<=Z<=qq<=C. All earlier physical labels in F, including arbitrarily many LARGE labels, are retained.

Put delta=ZZ-D, v=sum(F++[zpen]++T++[z]++E0), H0=v+delta, B=C-qq and low=H0-B. The eligible word is exactly the original-order filter of T++E0 by 0<s(i)<=B+1. Its total mass is assumed at least max(0,low). This condition supplies no subset, new endpoint, new gate or legal competitor.

If low<=0, select the empty return batch. Otherwise scan eligible entries in their physical order until the first cumulative sum reaches low. Such a crossing exists by the total-mass hypothesis. Before its last positive entry the integer sum is at most low-1, and that last entry is at most B+1. The resulting Rplus is an actual Sublist of eligible, with max(0,low)<=sum(Rplus)<=low+B=H0. The proof implements this first crossing by List induction, retaining physical occurrences rather than identifying equal numerical values.

Remove exactly Rplus from T++E0. Sublist implies the existing Subperm count bounds, and the standard List.diff permutation gives the complete remaining batch A0 with (A0++Rplus).Perm(T++E0). Original zpen legality gives the new departure b0=sum(F)-D in [0,C]. Put eta=H0-sum(Rplus). The selected bounds imply 0<=eta<=B. Hence e=eta+qq and c=eta+Z both lie in [0,C], with c<=e. The exact old-word mass identity gives b0+sum(A0)=c.

All entries of A0 remain SMALL. Every opposite SMALL pair has combined magnitude at most 2Q-2<C, so SmallStepOrdering.exists_order_between orders the WHOLE A0 between the proved b0 and c. It returns L and (L++Rplus).Perm(T++E0). The literal V=F++[n]++L++[z,q] preserves the physical zero-start F; z takes c to eta and q takes eta to e. Legal, InStrip from zero and every natural take bound, including zero and overlength takes, are proved outputs.

The literal returned list is R=[zpen]++Rplus++E1. The proved total-word permutation (V++R).Perm(W++[n,q]), old Nodup and actual whole-word unusedness produce the complete Inventory: new Nodup, exact disjoint used and unused partitions, exact source and complement sums, and the precise SMALL complement update. Repeated numerical weights at distinct physical labels remain distinct. No same-consumed-set transport is used.

Only zpen is returned LARGE, while n and q are inserted LARGE. Therefore G(V)+1=G(W), U(V)+1=U(W)+|Rplus|+|E1|, and H(V)+3^ZZ=H(W)+3^D+3^qq. The literal endpoint is v+delta+qq-sum(Rplus). Since the first objective coordinate G strictly decreases, J=(G,H,U) strictly decreases regardless of energy or all-unused count changes.

This theorem generalizes the concrete odd-boundary third exchange without requiring any p/a/rho relation. It proves the stated computable positive-return trigger, not universal trigger availability, signed-return completeness, general deep-suffix existence or full C3.1. Those wider statements remain OPEN.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/PositiveSmallReturnExchange.actualSource_positiveSmall_return_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/TerminalLargeSubstitution](TerminalLargeSubstitution.md)
