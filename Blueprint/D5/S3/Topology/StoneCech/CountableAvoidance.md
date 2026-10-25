# Countable avoidance and full Stone–Čech injection

## Abstract

Countable forbidden free ultrafilters can be avoided by one infinite subsequence.

**Theorem 1.1 (An infinite set missed by every forbidden free ultrafilter).**

$$\forall p: Nat \to \operatorname{Ultrafilter}\left(Nat\right), {\forall n: Nat, \operatorname{toFilter}\left(\operatorname{p}\left(n\right)\right) \le cofinite} \Rightarrow {\exists A: \operatorname{Set}\left(Nat\right), \operatorname{Infinite}\left(A\right) \land \forall n: Nat, \neg \operatorname{mem}\left(A, \operatorname{p}\left(n\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/CountableAvoidance.exists_infinite_notMem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every countable family p(n) of ultrafilters on Nat extending the cofinite filter, there is an infinite set A belonging to none of them. Start with Nat. Split each infinite pool into two disjoint infinite sets and choose a half absent from the next p(n). A diagonal infinite set is contained in each fixed later pool up to finitely many points. A free ultrafilter ignores those finite errors. The construction directly reuses PointPairSeparation.split_pool and diagonal_pool and requires no continuum or almost-disjoint-family hypothesis.

**Theorem 1.2 (Continuous reindexing).**

$$\forall A: Type, \forall B: Type, \forall j: A \to B, \operatorname{Continuous}\left(\operatorname{map}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/CountableAvoidance.continuous_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse image of the membership clopen for S is the membership clopen for the literal inverse image j inverse S.

**Theorem 1.3 (Removing all principal/free collisions).**

$$\forall Y: Type, \forall h: \operatorname{Ultrafilter}\left(Nat\right) \to Y, {\operatorname{Injective}\left(\operatorname{compose}\left(h, pure\right)\right)} \Rightarrow {{\operatorname{InjOn}\left(h, \{p : \operatorname{Ultrafilter}\left(Nat\right) \mid \operatorname{toFilter}\left(p\right) \le cofinite\}\right)} \Rightarrow {\exists j: Nat \to Nat, \operatorname{StrictMono}\left(j\right) \land \operatorname{Injective}\left(\operatorname{compose}\left(h, \operatorname{map}\left(j\right)\right)\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/CountableAvoidance.exists_strictMono_injective_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y is arbitrary and h need not be continuous. Assume h is injective on principal ultrafilters and separately injective on all free ultrafilters. For each principal value there is at most one colliding free point. Choose that point when it exists and a fixed free ultrafilter otherwise. Avoid this countable family by an infinite set A. On the clopen of ultrafilters containing A, principal/principal and free/free pairs retain injection, and both orientations of a principal/free pair are impossible. An increasing enumeration j of A therefore makes h composed with map j injective on the entire ultrafilter space.

ultrafilterHomeomorph identifies Ultrafilter A with StoneCech A for every discrete space A. Its forward map extends stoneCechUnit and its inverse extends pure; the two identities follow from agreement on the respective dense principal sets. This identifies the reindexed full domain with the ordinary Stone–Čech compactification. These facts do not by themselves construct a signed measure sequence or a CH compactum.

## References

- Truth anchor: `D5/S3/Topology/StoneCech/CountableAvoidance.continuous_map`
- Truth anchor: `D5/S3/Topology/StoneCech/CountableAvoidance.exists_infinite_notMem`
- Truth anchor: `D5/S3/Topology/StoneCech/CountableAvoidance.exists_strictMono_injective_reindex`
- Dependency: [D5/S3/Topology/ExtremallyDisconnected/PointPairSeparation](../ExtremallyDisconnected/PointPairSeparation.md)
