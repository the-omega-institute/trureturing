# Weighted row transfer

## Abstract

Weighted transfer of stress-three boundary words.

**Definition 1.1 (Column edge index).**

$$\forall p: Bool, \forall a: \operatorname{Fin}\left(6\right), \forall b: \operatorname{Fin}\left(6\right), \operatorname{index}\left(p, a, b\right) = 36\cdot \operatorname{toNat}\left(p\right)+6\cdot \operatorname{val}\left(a\right)+\operatorname{val}\left(b\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mask bit represents the parity and ordered pair of letters of a column edge.

**Definition 1.2 (Parity of an index).**

$$\forall n: \mathbb{N}, \operatorname{par}\left(n\right) = \operatorname{decide}\left((\operatorname{mod}\left(n, 2\right) = 1)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.par` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean is true at odd indices.

**Lemma 1.3 (Parity of the successor).**

$$\forall n: \mathbb{N}, \operatorname{par}\left(n+1\right) = \operatorname{not}\left(\operatorname{par}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.par_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each step in the column continuation count flips the parity.

**Definition 1.4 (Transfer state).**

$$State: Type$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record fields are parity of type Bool, last of type Fin 6, and mask of type Nat. The mask stores the surviving column edges, indexed by parity and the two letters.

**Definition 1.5 (Signed history).**

$$\forall \alpha: Type, \operatorname{Hist}\left(\alpha\right) = \operatorname{List}\left(\alpha \times \mathbb{Z}\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.Hist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A history is an ordered list of states with integer weights.

**Definition 1.6 (History evaluation).**

$$\forall \alpha: Type, \forall xs: \operatorname{Hist}\left(\alpha\right), \forall f: \alpha \to \mathbb{Z}, \operatorname{evalHist}\left(xs, f\right) = \operatorname{sum}\left(\operatorname{map}\left((\lambda (s,x), x\cdot f\left(s\right)), xs\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.evalHist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum includes the contribution of every list entry, including repeats.

**Definition 1.7 (Scaling a signed history).**

$$\forall \alpha: Type, \forall xs: \operatorname{Hist}\left(\alpha\right), \forall c: \mathbb{Z}, \operatorname{scaleHist}\left(c, xs\right) = \operatorname{map}\left((\lambda (s,x), (s, c\cdot x)), xs\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.scaleHist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Scaling multiplies every weight by the same integer and retains the list order.

**Definition 1.8 (Normalization).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)] normalize: (\alpha \to \mathbb{N}) \to \operatorname{Hist}\left(\alpha\right) \to \operatorname{Hist}\left(\alpha\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.normalize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The implementation merges singleton runs using the supplied natural-valued key, combines adjacent identical states, and drops zero weights.

**Definition 1.9 (State key).**

$$\forall s: State, \operatorname{stateKey}\left(s\right) = 12\cdot \operatorname{mask}\left(s\right)+6\cdot \operatorname{toNat}\left(\operatorname{parity}\left(s\right)\right)+\operatorname{val}\left(\operatorname{last}\left(s\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.stateKey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The key orders by mask, then parity, then last letter.

**Definition 1.10 (One transfer step).**

$$stepHist: \operatorname{Hist}\left(State\right) \to \operatorname{Hist}\left(State\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.stepHist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each weighted state and each next letter a, the new state flips parity, takes a as last letter, and intersects the mask with legal edges for that crossing. It retains the weight if a parity-zero edge out of column letter zero survives. Concatenate the surviving successors and normalize with stateKey.

**Definition 1.11 (Action on observables).**

$$action: (State \to \mathbb{Z}) \to State \to \mathbb{Z}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At state s, sum f on its surviving successors over the six choices of the next letter. The survival rule is the same one used by stepHist.

**Definition 1.12 (Row transfer history).**

$$\forall h: \mathbb{N}, \operatorname{path}\left(h+1\right) = \operatorname{stepHist}\left(\operatorname{path}\left(h\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function has type Nat to Hist State. At zero its list contains the six states in letter order, each with parity false, the corresponding last letter, all 72 mask bits set and weight one.

**Definition 1.13 (Signed coefficient history).**

$$\forall v: \mathbb{N} \to \operatorname{Hist}\left(State\right), \operatorname{coefficients}\left(v\right) = \operatorname{scaleHist}\left(1, v\left(10\right)\right) ++ \operatorname{scaleHist}\left(-3, v\left(9\right)\right) ++ \operatorname{scaleHist}\left(-17, v\left(8\right)\right) ++ \operatorname{scaleHist}\left(57, v\left(7\right)\right) ++ \operatorname{scaleHist}\left(86, v\left(6\right)\right) ++ \operatorname{scaleHist}\left(-372, v\left(5\right)\right) ++ \operatorname{scaleHist}\left(-76, v\left(4\right)\right) ++ \operatorname{scaleHist}\left(972, v\left(3\right)\right) ++ \operatorname{scaleHist}\left(-360, v\left(2\right)\right) ++ \operatorname{scaleHist}\left(-864, v\left(1\right)\right) ++ \operatorname{scaleHist}\left(576, v\left(0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terms are concatenated in descending index order.

**Definition 1.14 (Residual history).**

$$\forall h: \mathbb{N}, \operatorname{residualHist}\left(h\right) = \operatorname{normalize}\left(stateKey, \operatorname{coefficients}\left(\lambda i, \operatorname{path}\left(h+i+1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.residualHist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial index of the path window is h plus one.

**Definition 1.15 (Grouping by mask).**

$$\forall xs: \operatorname{Hist}\left(State\right), \operatorname{groupMask}\left(xs\right) = \operatorname{normalize}\left(id, \operatorname{map}\left((\lambda (s,x), (\operatorname{mask}\left(s\right), x)), xs\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.groupMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The result is a signed history over natural-number masks.

**Definition 1.16 (Acceptance at fixed width).**

$$\forall w: \mathbb{N}, \forall m: \mathbb{N}, \operatorname{value}\left(w, m\right) = \sum_{c\in \operatorname{Word}\left(w\right)} \operatorname{ite}\left((c\left(0\right) = 0 \land \forall j: \operatorname{Fin}\left(w\right), \operatorname{testBit}\left(m, 36\cdot \operatorname{mod}\left(\operatorname{val}\left(j\right), 2\right)+6\cdot \operatorname{val}\left(c\left(\operatorname{castSucc}\left(j\right)\right)\right)+\operatorname{val}\left(c\left(\operatorname{succ}\left(j\right)\right)\right)\right) = true), 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This integer sum counts words starting at zero whose consecutive column edges are all present in the mask. Test-bit returns a Boolean.

**Lemma 1.17 (Empty history).**

$$\forall \alpha: Type, \forall f: \alpha \to \mathbb{Z}, \operatorname{evalHist}\left([], f\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_nil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty history has zero evaluation.

**Lemma 1.18 (Concatenated histories).**

$$\forall \alpha: Type, \forall xs: \operatorname{Hist}\left(\alpha\right), \forall ys: \operatorname{Hist}\left(\alpha\right), \forall f: \alpha \to \mathbb{Z}, \operatorname{evalHist}\left(xs ++ ys, f\right) = \operatorname{evalHist}\left(xs, f\right)+\operatorname{evalHist}\left(ys, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation adds across concatenation.

**Lemma 1.19 (Evaluation after scaling).**

$$\forall \alpha: Type, \forall xs: \operatorname{Hist}\left(\alpha\right), \forall f: \alpha \to \mathbb{Z}, \forall c: \mathbb{Z}, \operatorname{evalHist}\left(\operatorname{scaleHist}\left(c, xs\right), f\right) = c\cdot \operatorname{evalHist}\left(xs, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every term acquires the same integer factor.

**Lemma 1.20 (Evaluation after normalization).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)] \forall key: \alpha \to \mathbb{N}, \forall xs: \operatorname{Hist}\left(\alpha\right), \forall f: \alpha \to \mathbb{Z}, \operatorname{evalHist}\left(\operatorname{normalize}\left(key, xs\right), f\right) = \operatorname{evalHist}\left(xs, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Merging the runs and combining equal states preserves evaluation for every observable.

**Lemma 1.21 (Evaluation by mask).**

$$\forall xs: \operatorname{Hist}\left(State\right), \forall f: \mathbb{N} \to \mathbb{Z}, \operatorname{evalHist}\left(\operatorname{groupMask}\left(xs\right), f\right) = \operatorname{evalHist}\left(xs, \lambda s, f\left(\operatorname{mask}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mask observable gives the same evaluation before and after grouping.

**Lemma 1.22 (Residual propagation).**

$$\forall h: \mathbb{N}, \forall f: State \to \mathbb{Z}, \operatorname{evalHist}\left(\operatorname{residualHist}\left(h+1\right), f\right) = \operatorname{evalHist}\left(\operatorname{residualHist}\left(h\right), \operatorname{action}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_residual_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Moving the residual window forward by one applies the transfer action to the observable.

**Theorem 1.23 (Transfer equals the literal count).**

$$\forall h: \mathbb{N}, \forall w: \mathbb{N}, 0<h \implies 0<w \implies (\operatorname{C}\left(3, 3, h, w\right): \mathbb{Z}) = \operatorname{evalHist}\left(\operatorname{path}\left(h\right), \lambda s, \operatorname{value}\left(w, \operatorname{mask}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

By the boundary-word equivalence, each row word contributes the number of compatible column words. At positive width, a discarded state has zero contribution.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.Hist`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.State`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.action`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.coefficients`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.count_transfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.evalHist`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_append`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_group`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_nil`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_normalize`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_residual_succ`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.eval_scale`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.groupMask`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.index`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.normalize`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.par`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.par_succ`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.path`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.residualHist`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.scaleHist`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.stateKey`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.stepHist`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Transfer.value`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding](HardinA235301Encoding.md)
