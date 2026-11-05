# Positive odd penultimate exchanges with genuine SMALL returns

## Abstract

Two explicit positive actual-source exchanges return the odd penultimate LARGE label and the crossing SMALL label, insert the genuinely unused n and q, and strictly lower G.

The two branches construct literal physical words from original append blocking and source-derived gates. The theorem retains every indicated SMALL batch and exports both exact disjoint physical partitions. The account below distinguishes this conditional positive boundary result from general favorable-path availability.

**Theorem 1.1 (Two conditional physical exchanges and their complete inventories).**

Lean statement: `D5/S3/Combinatorics/Circle/OddPenultimateExchange.actualSource_odd_penultimate_positive_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddPenultimateExchange.actualSource_odd_penultimate_positive_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scope is positive actual source s=actualSource(k,t), with k>=3, N=2^k-1, Q=2^(k-2), C=N/2, physical p,a,z and lists F,Tpre,Tpost,E0,E1. Put n=hit(k,1,p), q=finRotate(k,a), zpen=finRotate(k,q). The ORIGINAL word W=F++[zpen]++Tpre++[a]++Tpost++[z]++E0++E1 is Legal, n and q are unused in the entire W, and every label in Tpre++[a]++Tpost++E0++E1 is SMALL. The source assumptions are s(p)>0, n LARGE, N<3|s(p)|, 3s(a)>C+1, and s(q)<s(p). The terminal z is negative LARGE with -s(z)<=|s(n)|. No unusedness or append blocking of p is required.

The old pre-a height u=sum(F++[zpen]++Tpre) is less than D=|s(n)|. Appending n fails Legal both at W and at the actual terminal prefix W0=F++[zpen]++Tpre++[a]++Tpost++[z]++E0. These are old-word predicates, not supplied new endpoints. Original Legal and unusedness let the unchanged public TerminalLargeSubstitution.blocked_gate derive h=sum(W)<D and vE=sum(W0)<D. The scalar alternative supplied is Z<=u+delta OR s(a)-delta<=vE, where Z=-s(z) and delta=-s(zpen)-D.

All source geometry is derived: write P=s(p), aa=s(a), qq=s(q), ZZ=-s(zpen). Native geometry and the actual cycle equations give D=N-2P, 2P<=C+Q, qq=2aa, ZZ=N-2qq, and delta=ZZ-D=2(P-qq)>0. They imply 0<delta<aa, q and zpen LARGE, and qq>D>=Z. The actual old zpen gate yields the legal new departure b=sum(F)-D. For any old terminal height v in [0,D), the new endpoint v+2P-3aa is in [0,C]; no legal competitor or SMALL subset allocation is a premise.

If Z<=u+delta, select L.Perm(Tpre) from b to u+delta. The literal first word is V=F++[n]++L++[z,q]++M, with M.Perm(Tpost++E0++E1). The z gate follows from the selected scalar condition; the next height j=u+delta-Z+qq lies in [0,C]. Order the entire remaining SMALL batch M from j to h+2P-3aa. The physical returned list is exactly [zpen,a]. This branch retains every other old physical label.

Otherwise the old scalar alternative gives eta=vE+delta-aa>=0. The final eta+qq=vE+2P-3aa is legal. Since qq>D>=Z, the required SMALL endpoint before z, eta+Z, is legal as well. Select L.Perm(Tpre++Tpost++E0) from b to eta+Z. The literal second word is V=F++[n]++L++[z,q]; M is empty and the actual returned list is [zpen,a]++E1. Thus any chosen actual terminal prefix through E0 meeting the condition supplies the second construction, with its genuine remaining SMALL suffix E1 returned.

SmallStepOrdering.exists_order_between is used only after both endpoints have been derived. Every opposite SMALL pair has combined magnitude at most 2Q-2<C. Perm preserves the complete physical batches, including zero-valued SMALL labels and equal-valued distinct labels. The original F stays in its physical order and at its original zero start. The output proves Legal, InStrip from zero, and every natural take bound, including empty and overlength takes.

The proved total-word permutation (V++R).Perm(W++[n,q]), old Nodup and actual whole-word unusedness produce the full Inventory: exact disjoint used and unused partitions, new Nodup, source and complement sums, and the exact SMALL complement update. Both branches satisfy G(V)+1=G(W) and H(V)+3^ZZ=H(W)+3^D+3^qq. The first has U(V)=U(W); the second has U(V)=U(W)+|E1|. These exact identities imply strict J descent already at its first coordinate G, irrespective of the energy difference. The endpoint is h+2P-3aa in the first branch and vE+2P-3aa in the second.

This is a conditional positive-orientation theorem for the concrete odd boundary finRotate(q)=zpen. It does not show that every odd consumed boundary is penultimate or that every penultimate instance meets the scalar alternative. Negative orientation, universal deep-suffix availability, the residual region excluding both constructions, and full C3.1 remain outside this declaration. The only added parent API dependency is blocked_gate made public with its original telescope. Existing exact integer controls realize both branches, including a second-only case returning a nonempty SMALL suffix; those finite controls are not a universal availability proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/OddPenultimateExchange.actualSource_odd_penultimate_positive_exchange_full`
- Dependency: [D5/S3/Combinatorics/Circle/TerminalLargeSubstitution](TerminalLargeSubstitution.md)
