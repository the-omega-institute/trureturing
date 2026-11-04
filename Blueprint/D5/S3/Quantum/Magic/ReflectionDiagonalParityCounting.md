# Counting even labels in a CNOT sequence

## Abstract

Visiting every nonzero even Boolean label between odd initial and final wire labels requires exponentially many updates and a linear return cost.

**Definition 1.1 (Updating a target label).**

$$\forall \left(m: \mathbb{N}\right), \forall \left(ls: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right)\right), \forall \left(p: \left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right), \operatorname{update}\left(ls, p\right) = \operatorname{Function.update}\left(ls, \operatorname{Prod.fst}\left(p\right), ls\left(\operatorname{Prod.fst}\left(p\right)\right) + ls\left(\operatorname{Prod.snd}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.update` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each wire carries a Boolean vector. The ordered pair p specifies the target first and the control second; replace the target label by the sum of those two labels and keep every other label. Addition of Boolean vectors is coordinatewise exclusive-or. The definition is valid for every ordered pair, including equal coordinates.

**Definition 1.2 (The final wire labels).**

$$\forall \left(m: \mathbb{N}\right), \forall \left(gs: \operatorname{List}\left(\left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right)\right), \forall \left(ls: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right)\right), \operatorname{labels}\left(gs, ls\right) = \operatorname{List.foldl}\left(\operatorname{update}, ls, gs\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.labels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from ls, apply the updates in the list gs from left to right. The result records every final wire label. No independence or invertibility of the initial label vectors is assumed.

**Definition 1.3 (The chronological list of target outputs).**

$$\forall \left(m: \mathbb{N}\right), \left(\operatorname{outputs}\left(\left(\operatorname{List.nil}: \operatorname{List}\left(\left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right)\right)\right) = \operatorname{Function.const}\left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right), \left(\operatorname{List.nil}: \operatorname{List}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right)\right)\right)\right) \land \left(\forall \left(p: \left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right), \forall \left(gs: \operatorname{List}\left(\left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right)\right), \forall \left(ls: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right)\right), \operatorname{outputs}\left(\operatorname{List.cons}\left(p, gs\right), ls\right) = \operatorname{List.cons}\left(ls\left(\operatorname{Prod.fst}\left(p\right)\right) + ls\left(\operatorname{Prod.snd}\left(p\right)\right), \operatorname{outputs}\left(gs, \operatorname{update}\left(ls, p\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.outputs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each update, record the new target vector before continuing with the updated wire labels. The empty update list has no outputs. The list retains repeated vectors and has one entry per update; it does not include the initial vectors. A right fold constructs the function of the current label array: each step prepends its target output and passes the updated array to the remaining steps.

**Theorem 1.4 (Visiting all even vectors forces a return cost).**

$$\forall \left(m: \mathbb{N}\right), \left(0 < m\right) \Rightarrow \left(\forall \left(gs: \operatorname{List}\left(\left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right)\right), \forall \left(ls: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \sum_{\left(i: \operatorname{Fin}\left(m\right)\right)} \left(ls\left(j, i\right)\right) = \operatorname{Bool.true}\right) \Rightarrow \left(\left(\forall \left(j: \operatorname{Fin}\left(m\right)\right), \sum_{\left(i: \operatorname{Fin}\left(m\right)\right)} \left(\operatorname{labels}\left(gs, ls\right)\left(j, i\right)\right) = \operatorname{Bool.true}\right) \Rightarrow \left(\left(\forall \left(v: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right), \left(\sum_{\left(i: \operatorname{Fin}\left(m\right)\right)} \left(v\left(i\right)\right) = \operatorname{Bool.false}\right) \Rightarrow \left(\left(v \ne \left(0: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}\right)\right) \Rightarrow \left(v \in \operatorname{outputs}\left(gs, ls\right)\right)\right)\right) \Rightarrow \left(2^{m - 1} + m - 2 \le \operatorname{List.length}\left(gs\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume m is positive, every initial and final wire label has odd Boolean coordinate sum, and every nonzero even vector occurs among the target outputs. Exactly half of all Boolean vectors are even: delete a final coordinate, and recover it as the Boolean sum of the remaining coordinates. After removing the zero vector, the number of distinct required vectors bounds the length of the list of even target outputs from below.

Call an update with odd target and odd control a birth. Its new target is even. The sums of sublists of the birth outputs include zero and every birth output, are closed under addition, and number at most two raised to the number of birth updates. Induction over the updates shows that every even vector present on a wire or appearing as an output belongs to this span. For an even target output, either both input vectors were even and closure under addition applies, or both were odd and the output is a birth. Since there are no even initial labels and every nonzero even vector appears, the span contains the whole even subspace. Its cardinality bound and strict growth of powers of two force at least m minus one birth updates.

Count the wires with even labels. A birth increases this number by one, and an update with even target and odd control decreases it by one; all other combinations of odd and even labels leave it unchanged. Induction gives the exact balance: the final even-wire count plus the number of decreases equals the initial even-wire count plus the number of birth updates. Both endpoint counts are zero, so there are as many decreases as birth updates, hence at least m minus one decreases. Every decrease has an odd target output and is therefore disjoint from the updates counted by even outputs. Adding the two counts gives the displayed lower bound, with subtraction in the natural numbers.

## References

- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.count_bound`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.labels`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.outputs`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.update`
