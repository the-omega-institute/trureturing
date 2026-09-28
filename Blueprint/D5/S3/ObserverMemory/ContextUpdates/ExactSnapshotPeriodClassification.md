# Exact Snapshot Period Classification

## Abstract

Exact snapshots have common binary sender periods and even global switches.

**Theorem 1.1 (Sender periods and the global even-switch group).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotPeriodClassification.period_classification`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotPeriodClassification.period_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be an additive commutative group, I a finite sender set with at least two members, and chi an additive homomorphism from G to ZMod 2. A source is ((a,x),h), where a is the receiver coordinate, x maps I to G, and h belongs to ker chi. Its target is Y = a + sum_i x_i and its clock is t = Y+h. A protocol has a deterministic query q(a,t) and replies e_i(x_i,t,c), with arbitrary, possibly different, reply alphabets. Separating the receiver from I identifies the source space with G^r times ker chi, where r=card(I)+1 is at least three.

For every reachable branch (a,t,c), every sender i and every x in G, there exists one actual source with receiver a, clock t, query c and sender coordinate x_i=x. Choose a different sender j, assign it t-a-x, set all remaining sender coordinates to zero, and take h=0. This calculation needs neither exact decoding nor surjectivity of chi and permits infinite G.

Assume a decoder D recovers Y from the entire snapshot O=(a,t,(e_i(x_i,t,q(a,t)))_i). Every sender input is realizable on every reachable branch, together with the following classification. Define P_i to contain precisely those p for which e_i(x+p,t,c)=e_i(x,t,c) for every x and every reachable branch (a,t,c). Define K to contain the source translations v satisfying O(s+v)=O(s) for every actual source s. No closed update of O is assumed.

Each P_i is either the zero subgroup or {0,tau_i}, where tau_i is nonzero, chi(tau_i)=1, and tau_i+tau_i=0. Every two nonzero elements drawn from any two P_i are equal. Consequently all nontrivial sender period groups share one generator. No generator is chosen when all P_i are trivial.

Writing a translation as v=((b,u),k), membership in K is equivalent to b=0, k=0, u_i in P_i for every sender i, and sum_i u_i=0. Let J be the set of senders with P_i nontrivial. If card(J) is at most one, K is the zero subgroup. Whenever J is nonempty, K is additively equivalent to the group of functions J to ZMod 2 whose sum is zero, and card(K) equals 2^(card(J)-1). These functions select an even number of the common order-two generator. The statement includes the singleton case.

To constrain the periods, take any vector u_i in P_i with chi(sum_i u_i)=0. The source ((0,u),-sum_i u_i) has the same zero clock, query and replies as the zero source. Exact decoding forces sum_i u_i=0. Applying this to one or two supported coordinates establishes the kernel restriction, order-two property and common generator. Local realizability then identifies every coordinate of a global period. Restricting chi to the active sender coordinates gives the additive equivalence; summing the binary coordinates has a kernel of index two when J is nonempty.

The quantifiers range over all actually used branches. A collision on one branch that is absent from their intersection contributes no global period. The group G and the alphabets may be infinite, so the result includes all finite message alphabets and, in particular, every surjective binary character.

## References

- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotPeriodClassification.period_classification`
