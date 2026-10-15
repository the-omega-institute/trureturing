# Actual witness tables for preselected and stopped acquisitions

## Abstract

Actual witness executions extract a common finite scheduled table law.

**Definition 1.1 (Chronological schedule cells).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.view`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.view` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary address type, Boolean stop mode, finite address list and static Boolean response map, view returns every scheduled reply in order. In stopped mode it includes the first false reply and omits everything after it. In preselected mode it retains every reply, including repeated addresses and reversed pairs.

**Theorem 1.2 (Chronological view congruence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.view_congr`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.view_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every address type A, stop mode, finite list xs and Boolean reply maps q,r on A, agreement q(i)=r(i) for every occurrence i in xs implies view stop xs q equals view stop xs r. List induction retains order, repetitions and first-false stopping. Equal-rank chain words use this congruence through the actual catalog factorization.

**Definition 1.3 (Actual requests and silent processing).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.step`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arbitrary configuration C contains the eventual original tape. A source-free instruction reads an arbitrary natural address, silently updates C, or halts. The adapter to StateTransition appends exactly one address-reply pair at every read, including a duplicate. Silent updates preserve this log. There is no countability, computability, measurable-space or transition-time hypothesis on C. The update epochs of GuardedPhaseExecution are not request counts.

**Definition 1.4 (Reachable next-query discipline).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.Disciplined`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.Disciplined` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each fixed seed and source, a reachable read must be the next entry of the seed-preselected schedule, after the entire chronological address log. In stopped mode every earlier recorded reply must be true. Silent processing is unrestricted. This necessary local condition follows directly from either original schedule contract; it also permits early handoff, so the extraction theorem covers those rules too. It assumes no equality of executions, terminal factorization or finite table membership. A read after a queried zero is excluded by its local premise.

**Definition 1.5 (Retaining original low addresses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.lowSchedule`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.lowSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter a finite schedule by address less than L, preserving order and repeats. Natural address i means original prime index i+1. The filtered length is at most the original length, and a strictly increasing original list remains strictly increasing.

**Definition 1.6 (Finite input words).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.lowReply`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.lowReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word b on Fin L gives its actual Boolean reply below L. The default value outside this range is false and serves only to evaluate low schedules. This is an offline finite table definition, not an additional observation available to the acquisition.

**Definition 1.7 (The complete restricted output catalog).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.InCatalog`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.InCatalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any stop mode and L, a finite output function belongs to the catalog when some at-most-two low-address schedule determines it through its reply cell. The stopped schedule is strictly increasing. Every cell may have any label in Fin(L+1), independently of whether its mark was queried. The preselected pair has all four cells 00,01,10,11; repeats have diagonal information and reversal preserves its actual order. The stopped pair has cells 0,10,11, so words 00 and 01 share one cell. Empty and singleton schedules are included, as is L=0.

**Definition 1.8 (One whole-table gate).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.witnessTable`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.witnessTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a seed event D, measurable sourcewise terminal maps phi and marked projection rho, the whole output table at s evaluates rho(phi(b,s)) for every b on D. Off D the entire table is the constant base label zero. Thus every input uses the same gate and the same original seed. The witness executions used to define this table are fixed actual comparison sources chosen before seeds; evaluating them is not a live source acquisition.

**Definition 1.9 (Finite representatives and a common law).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.Catalog`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.Catalog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The catalog is the subtype of all complete word-to-label functions satisfying InCatalog. It is finite because both the word set and label set are finite. A representing schedule may be fixed once for each function by its defining existential. Pushing one seed law to this subtype gives one PMF of whole tables, rather than separate distributions for different input words.

**Definition 1.10 (A common schedule bound).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.scheduleGate`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.scheduleGate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At cutoff c, scheduleGate is the event that every preselected address is strictly less than c. Its measurability is the required consequence of measurable finite schedule selection. Its complement decreases to the empty set, because each individual seed chooses a finite schedule. No handoff time or configuration measurability is involved.

**Theorem 1.11 (One common catalog law approximates every actual witness row).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.scheduled_witness_approximation`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.scheduled_witness_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix arbitrary measurable seed and tape spaces S and Theta, an arbitrary configuration type C, a probability measure mu, active length L and Boolean stop mode. Fix one seed-dependent schedule, initialization and source-free instruction function, and a source-free terminal readout from C to Theta. For each m and each complete low word b, fix a static actual-witness response map q, a measurable terminal extension phi, a measurable conull termination event T, and an original target measure. Set cutoff c=L+1+m. The response is b below L and false on L through c-1. Require at most two schedule entries, strict increase in stopped mode, measurable schedule sublevel events, local reachable read discipline, finite evaluation on T, and equality of the terminal configuration readout with phi there. Require measurable rho from the full tape space to Fin(L+1), and the original sourcewise cap in supremum-over-events TV.

Let H_m be the one schedule event and D_m=H_m intersect the intersection of T_m,b over all low words. The theorem gives gamma_m=mu(H_m complement) tending to zero. For every m it constructs a measurable F_m:S to Catalog and one PMF w_m, with w_m.toMeasure=mu.map(F_m). Its entire function at every seed is the gated witnessTable. The failure mass is exactly mu(D_m complement)=gamma_m, and every row of the same w_m obeys TV(row_b,rho_*target_m,b)<=eps+gamma_m. No monotonicity of D_m is claimed; the actual comparison witnesses can change with m.

For replay relate equal configurations and equal chronological logs reachable in the first execution. Every recorded reply equals its source response. At a reachable next query the local schedule decomposition identifies its position; equality of preselected views, or of stopped views before a shared first zero, identifies that reply. The resulting local Respects relation is consumed by Mathlib StateTransition.tr_eval. It preserves the terminal configuration and therefore its original tape. Removing fixed high false replies preserves equality of low views. Filtering the schedule then proves catalog membership. This is local queried-cell replay: entire-prefix source agreement from Lemma 45.3 is not used in its place.

Finite coordinate measurability makes F_m measurable. All finite termination events intersect conullly, so discarding them adds no failure mass. On D_m every row equals the projected actual terminal map; event preimage inclusions bound its TV discrepancy by gamma_m. Triangle inequality and measurable TV contraction give the cap estimate. The TV object is the supremum of the maximum of both truncated event-mass differences in ENNReal, with no factor of two. For probability laws its real value is the original event-supremum absolute difference, and eps is the nonnegative real cap embedded in ENNReal.

## Original Fibonacci sources and limits

For the actual source take q_m,b(i)=1[p_(i+1) divides 1+F_r g], with r prime and ceil(F_r/10)<=g<=floor(F_r/5). FiniteFibonacciRankClosure directly supplies rankWitness. Applying Mathlib finite CRT and FibonacciRank.fibonacci_entry_point to these ranks supplies the finite-pattern window assembly: at K=1, one common R works for every prime r>=R and every Boolean pattern, with positive N. The whole finite family is fixed before seeds. Apply it to the first c primes, retaining b below L and zero at the other c-L addresses. In particular an all-positive low word has actual first absence L+1, rather than being an infinite all-positive source. The terminal maps and conull events are the sourcewise extensions of Definition 45.1. Take the full original disjoint union of B_j and P_j interval blocks as Theta, with marks theta_j=(B_1,1/(j+2)); rho fixes the retained positive marks and sends every other tape to label zero. No competitor output-support restriction is imposed.

Represent the entire original tape carrier by the sum of two copies of PNat times the real open unit interval. The measurable equivalence sumProdDistrib identifies it bijectively with a pair consisting of a tagged positive block index and an interval coordinate. The positive-index coordinate has its discrete sigma algebra; measurable_from_prod_countable_right identifies measurable blockwise maps with maps on this countable disjoint union. No interval coordinate is removed. The original consumer is Sum.elim of constant unknown on the left and the positive block index proposal on the right. Every theta_j has left tag, index one, and coordinate 1/(j+2), so the unchanged consumer returns unknown at every mark.

Reciprocal injectivity and natural-number casting give distinct marks. Their singletons are Borel measurable, as are finite unions and images. Embed Fin(L+1) by j to theta_j; this finite injective map is a measurable embedding. Define rho as Function.extend of its inverse labels with constant zero outside its range. MeasurableEmbedding.measurable_extend proves measurability on the full carrier. Injective.extend_apply gives rho(theta_j)=j for j<=L, and extend_apply' gives zero at every other tape. Including theta_0 in the embedding only assigns the same default label zero to that base point.

Use zero-based natural addresses: i reads p_(i+1), and a(i) denotes the original amplitude a_(i+1). For every actual source, positive N follows from its window lower bound. A prime larger than N cannot divide it, so Nat.find defines its least false address. For a low word b, define k as the least false address of lowReply b; it satisfies k<=L. The witness's actual first false address equals k: the low answers coincide below L and the forced answer at L is false. Thus a low zero gives actual first absence k+1, while an all-positive low word gives exactly L+1. This includes L=0 and retains every later-zero pattern.

Write the original selected measure as ofReal(1-a(k))*dirac(theta_0)+ofReal(a(k))*dirac(theta_(k+1)). Antitonicity and a(0)<=1 derive every needed amplitude upper bound from the original sequence contract. Map addition, scalar multiplication and Dirac measures through rho. If k<L, its image is the retained two-point eta_b; if k=L, both atoms map to zero and their coefficients sum to one, giving delta_0. This proves fixed eta_b independently of m, rather than assuming it. Applying scheduled_witness_approximation to the actual witness family and then finite simplex compactness produces one exact cap-feasible PMF on the same restricted catalog.

Each finite cap bounds both directed event discrepancies. Test the base singleton, the first-zero singleton, and their union separately. The resulting three inequalities are ofReal(1-a(k))<=eps+p_b({0}), ofReal(a(k))<=eps+p_b({k+1}), and 1<=eps+p_b({0,k+1}). The all-positive row is 1<=eps+p_b({0}). The pair row is an independent event test, with no inference from only singleton constraints. For probability measures and a nonnegative real cap, converting these finite ENNReal inequalities to real values gives the original closed rows without a factor of two. The necessity conclusion concerns finite feasibility and does not preserve every law of an arbitrary original competitor.

Definition 90.1 supplies the schedule discipline with all actual requests counted; its prescribed exhaustion and first-zero stopping imply the weaker local conditions used here. The original deterministic procedure supplies C, initial and prog after fixing the seed, with its terminal tape in C. Initialization and actions use the common seed and fixed zero advice; the source label, numerical N, first absence, target law and extra observations are absent. Only a read reply depends on the actual source. The interpreter retains arbitrary silent processing before and after reads. The extracted comparison tables do not run the consumer. OriginalScheduledRealization supplies the actual execution and same-source consumer handoff.

The unit proves class-preserving whole-table approximation, not Theorem 110.2's full equivalence. For fixed projected targets eta_b, the approximation supplies exact closed-cap finite feasibility: enumerate the finite catalog by Fin N, regard its PMFs as probability measures, and take a convergent subsequence in the compact simplex. Every discrete event mass is continuous; rewriting each TV constraint as its two event inequalities and passing to the limit gives TV(row_b,eta_b)<=eps for every word. Mapping the limit weights back through the enumeration keeps the same restricted catalog. For the original selected laws, this closed-cap application uses the full-carrier projection and first-absence parameter map above. OriginalScheduledRealization supplies actual scheduled prime reads and same-source marked-tape handoff. The OriginalScheduledRealization application combines a uniform interval sampler with the exact full-tail maximum identity and strict active cutoff, including the equality tail endpoint, to realize every cap-feasible distribution on the appropriate restricted catalog. Identifying the stopped catalog laws with the coefficient criterion O_L=C_L of Section 109.1 remains separate. L=0 is present in the theorem without a positive-length hypothesis. This result preserves feasibility information, not arbitrary original competitor laws, and gives no unrestricted N/O separation.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.Catalog`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.Disciplined`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.InCatalog`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.lowReply`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.lowSchedule`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.scheduleGate`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.scheduled_witness_approximation`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.step`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.view`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.view_congr`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.witnessTable`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle](../../../Estimation/DataProcessing/MeasurableTotalVariationTriangle.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution](../GuardedPhaseExecution.md)
