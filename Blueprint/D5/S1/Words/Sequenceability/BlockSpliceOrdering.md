# An old edge cut after a block splice

## Abstract

Block surgery on a directed cycle with distinct vertices and labels.

**Theorem 1.1 (Exact complementary labels and separated prefixes).**

$$\forall G \in Type,\; [AddCommGroup\left(G\right)] \forall z \in Nat \to G,\; \forall c \in Nat \to G,\; \forall N \in Nat,\; \forall k \in Nat,\; \forall t \in Nat,\; (2 \le k) \Rightarrow ((k \le t) \Rightarrow ((t < N) \Rightarrow ((InjOn\left(z, Iio\left(N\right)\right)) \Rightarrow ((InjOn\left(c, Iio\left(N\right)\right)) \Rightarrow ((\forall i \in Nat,\; (i < N) \Rightarrow (c\left(i\right) = z\left(mod\left(i + 1, N\right)\right) - z\left(i\right))) \Rightarrow ((z\left(k\right) - z\left(0\right) = c\left(t\right)) \Rightarrow (\exists P \in Nat \to G,\; \exists w \in List\left(G\right),\; (Perm\left(map\left(P, range\left(N - k + 1\right)\right), map\left(z, cons\left(0, rangeFrom\left(k, N - k\right)\right)\right)\right)) \land ((Nodup\left(map\left(P, range\left(N - k + 1\right)\right)\right)) \land ((w = map\left(\operatorname{fun} (i: Nat) \mapsto P\left(i + 1\right) - P\left(i\right), range\left(N - k\right)\right)) \land ((\forall j \in Nat,\; (j \le N - k) \Rightarrow (sum\left(take\left(j, w\right)\right) = P\left(j\right) - P\left(0\right))) \land ((Perm\left(w, map\left(c, rangeFrom\left(k, N - k\right)\right)\right)) \land ((Nodup\left(w\right)) \land ((length\left(w\right) = N - k) \land ((Injective\left(\operatorname{fun} (j: Fin\left(length\left(w\right) + 1\right)) \mapsto sum\left(take\left(val\left(j\right), w\right)\right)\right)) \land ((\forall i \in Nat,\; \forall j \in Nat,\; (i < j) \Rightarrow ((j \le length\left(w\right)) \Rightarrow (sum\left(take\left(j - i, drop\left(i, w\right)\right)\right) \ne 0))) \land ((sum\left(w\right) = -c\left(t\right)) \land (sum\left(w\right) \ne 0)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/BlockSpliceOrdering.block_splice_ordering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be any additive commutative group. Distinct cyclic vertices z(0),...,z(N-1) have distinct labels c(i)=z((i+1) mod N)-z(i). For 2 <= k <= t < N, assume the chord z(k)-z(0) equals c(t). The construction cuts the old edge indexed by t and retains the new chord. It orders exactly the labels c(k),...,c(N-1), each once. All bounded prefix sums, including empty and full prefixes, are distinct; every nonempty bounded interval has nonzero sum. The full sum is -c(t) and is nonzero.

The explicit path traverses z(t+1),...,z(N-1), then z(0), then z(k),...,z(t). Its label indices are t+1,...,N-1, then t for the new chord, then k,...,t-1. The three disjoint index blocks prove both inventories and distinctness. The initial block can be empty when t=N-1, and the last label block can be empty when t=k, including simultaneous emptiness. The label equality identifies values, not edge occurrences. No distinction between old and new label values, or restriction on characteristic, is assumed.

The result also returns a path P whose bounded vertices permute z(0),z(k),...,z(N-1), with no repetitions. The word consists of consecutive differences of P. Existing list telescoping gives every prefix as P(j)-P(0); prefix splitting then proves the interval assertion. In the displayed formula, rangeFrom(k,n) denotes List.range' k n, map takes the function first, and take and drop take the count first. List operations otherwise have their usual meanings. The statement is a general cycle surgery result; finite-field primitive elements, independence and transport to a prescribed frame are separate premises needed to apply it to independent omitted vectors.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/BlockSpliceOrdering.block_splice_ordering`
