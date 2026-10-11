# The sl2 action on two-wall words

## Abstract

The two binary arcs between two cyclic walls carry an sl2 action that descends to literal words and has the physical lowering operator.

Let K be a field of characteristic zero and let a,b be natural numbers. Use the literal counted words, marked cover, binary coordinates and maps Q,S,Jstar of TwoWallWords and TwoWallMarked. A coordinate c has entries p,m,n,u,v with m+n=a+b and ones(u)+ones(v)=b. True is letter two and false is letter one. Every finite sum below is over bonds, preserving transition multiplicities. Fin(m−1) is empty for m=0 or m=1; subtraction in these index bounds is natural subtraction. Binary positions have zero-based indices, so the coefficient associated with j is (j+1)(m−j−1).

**Definition 1.1 (Swapping an inner bond of the first arc).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{m}\left(c\right) - 1\right),\; \operatorname{leftMove}\left(c, j\right) = (\operatorname{p}\left(c\right), \operatorname{m}\left(c\right), \operatorname{n}\left(c\right), ((i : \operatorname{Fin}\left(\operatorname{m}\left(c\right)\right)) \mapsto \operatorname{u}\left(c\right)\left(\operatorname{EquivSwap}\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{m}\left(c\right)\right), \operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{m}\left(c\right)\right)\right)\left(i\right)\right)), \operatorname{v}\left(c\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.leftMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exchange entries j and j+1 of u. Keep p,m,n and v. The exchange preserves the number of true entries, so the filling certificate remains valid.

**Definition 1.2 (Swapping an inner bond of the second arc).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{n}\left(c\right) - 1\right),\; \operatorname{rightMove}\left(c, j\right) = (\operatorname{p}\left(c\right), \operatorname{m}\left(c\right), \operatorname{n}\left(c\right), \operatorname{u}\left(c\right), ((i : \operatorname{Fin}\left(\operatorname{n}\left(c\right)\right)) \mapsto \operatorname{v}\left(c\right)\left(\operatorname{EquivSwap}\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{n}\left(c\right)\right), \operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{n}\left(c\right)\right)\right)\left(i\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.rightMove` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exchange entries j and j+1 of v and retain the first arc. Both operations also apply to unequal entries in either orientation.

**Definition 1.3 (The marked weight operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{markedH}\left(K, a, b\right)\left(\operatorname{markedDelta}\left(K, \operatorname{encode}\left(c\right)\right)\right) = (\operatorname{cast}\left(\operatorname{weight}\left(\operatorname{u}\left(c\right)\right), K\right) + \operatorname{cast}\left(\operatorname{weight}\left(\operatorname{v}\left(c\right)\right), K\right)) \cdot (\operatorname{markedDelta}\left(K, \operatorname{encode}\left(c\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.markedH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the existing rational bin weights acts diagonally on the marked delta basis. Each rational scalar is cast to K. These basis images determine the linear endomorphism.

**Definition 1.4 (The marked raising operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{markedE}\left(K, a, b\right)\left(\operatorname{markedDelta}\left(K, \operatorname{encode}\left(c\right)\right)\right) = \sum_{j\in\operatorname{Fin}\left(\operatorname{m}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{m}\left(c\right)\right)\right) = \operatorname{false}) \land (\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{m}\left(c\right)\right)\right) = \operatorname{true})), ((\operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right)) \cdot (\operatorname{cast}\left(\operatorname{m}\left(c\right), K\right) - \operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right))) \cdot (\operatorname{markedDelta}\left(K, \operatorname{encode}\left(\operatorname{leftMove}\left(c, j\right)\right)\right)), 0\right)) + \sum_{j\in\operatorname{Fin}\left(\operatorname{n}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{n}\left(c\right)\right)\right) = \operatorname{false}) \land (\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{n}\left(c\right)\right)\right) = \operatorname{true})), ((\operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right)) \cdot (\operatorname{cast}\left(\operatorname{n}\left(c\right), K\right) - \operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right))) \cdot (\operatorname{markedDelta}\left(K, \operatorname{encode}\left(\operatorname{rightMove}\left(c, j\right)\right)\right)), 0\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.markedE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each arc, sum the enabled 12 to 21 transitions with coefficient (j+1)(m−j−1). The distinguished wall remains fixed. These basis images determine the linear endomorphism.

**Definition 1.5 (The marked lowering operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{markedF}\left(K, a, b\right)\left(\operatorname{markedDelta}\left(K, \operatorname{encode}\left(c\right)\right)\right) = \sum_{j\in\operatorname{Fin}\left(\operatorname{m}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{m}\left(c\right)\right)\right) = \operatorname{true}) \land (\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{m}\left(c\right)\right)\right) = \operatorname{false})), \operatorname{markedDelta}\left(K, \operatorname{encode}\left(\operatorname{leftMove}\left(c, j\right)\right)\right), 0\right)) + \sum_{j\in\operatorname{Fin}\left(\operatorname{n}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{n}\left(c\right)\right)\right) = \operatorname{true}) \land (\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{n}\left(c\right)\right)\right) = \operatorname{false})), \operatorname{markedDelta}\left(K, \operatorname{encode}\left(\operatorname{rightMove}\left(c, j\right)\right)\right), 0\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.markedF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each arc, sum the enabled 21 to 12 transitions with coefficient one. The distinguished wall remains fixed. These basis images determine the linear endomorphism.

**Definition 1.6 (Descending the weight operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{h}\left(K, a, b\right) = (\operatorname{inverse}\left(\operatorname{cast}\left(2, K\right)\right)) \cdot (\operatorname{comp}\left(\operatorname{Q}\left(K, a, b\right), \operatorname{comp}\left(\operatorname{markedH}\left(K, a, b\right), \operatorname{S}\left(K, a, b\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply S, then the marked weight operator, then Q, and multiply by the inverse of two in K.

**Definition 1.7 (Descending the raising operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{e}\left(K, a, b\right) = (\operatorname{inverse}\left(\operatorname{cast}\left(2, K\right)\right)) \cdot (\operatorname{comp}\left(\operatorname{Q}\left(K, a, b\right), \operatorname{comp}\left(\operatorname{markedE}\left(K, a, b\right), \operatorname{S}\left(K, a, b\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the same descent formula to the marked raising operator.

**Definition 1.8 (Descending the lowering operator).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{f}\left(K, a, b\right) = (\operatorname{inverse}\left(\operatorname{cast}\left(2, K\right)\right)) \cdot (\operatorname{comp}\left(\operatorname{Q}\left(K, a, b\right), \operatorname{comp}\left(\operatorname{markedF}\left(K, a, b\right), \operatorname{S}\left(K, a, b\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the same descent formula to the marked lowering operator.

**Definition 1.9 (The integer inversion weight).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{integerWeight}\left(c\right) = (2) \cdot (\operatorname{cast}\left(\operatorname{level}\left(\operatorname{u}\left(c\right)\right), \mathbb{Z}\right)) - (\operatorname{cast}\left(\operatorname{ones}\left(\operatorname{u}\left(c\right)\right), \mathbb{Z}\right)) \cdot (\operatorname{cast}\left(\operatorname{m}\left(c\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{ones}\left(\operatorname{u}\left(c\right)\right), \mathbb{Z}\right)) + (2) \cdot (\operatorname{cast}\left(\operatorname{level}\left(\operatorname{v}\left(c\right)\right), \mathbb{Z}\right)) - (\operatorname{cast}\left(\operatorname{ones}\left(\operatorname{v}\left(c\right)\right), \mathbb{Z}\right)) \cdot (\operatorname{cast}\left(\operatorname{n}\left(c\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{ones}\left(\operatorname{v}\left(c\right)\right), \mathbb{Z}\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallSl2.integerWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function level is the existing count of ordered 2-before-1 pairs. The function ones counts the twos, and length minus ones counts the ones. Both subtractions inside the weight are in the integers. The two arc contributions add and are independent of which wall is marked.

**Theorem 1.10 (Relations, physical identification and basis formulas).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\operatorname{Sl2Relations}\left(\operatorname{markedH}\left(K, a, b\right), \operatorname{markedE}\left(K, a, b\right), \operatorname{markedF}\left(K, a, b\right)\right)) \land (((\operatorname{Commute}\left(\operatorname{Jstar}\left(K, a, b\right), \operatorname{markedH}\left(K, a, b\right)\right)) \land ((\operatorname{Commute}\left(\operatorname{Jstar}\left(K, a, b\right), \operatorname{markedE}\left(K, a, b\right)\right)) \land ((\operatorname{Commute}\left(\operatorname{Jstar}\left(K, a, b\right), \operatorname{markedF}\left(K, a, b\right)\right)) \land (\forall t \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{Commute}\left(\operatorname{markedTranslation}\left(K, t\right), \operatorname{markedH}\left(K, a, b\right)\right)) \land ((\operatorname{Commute}\left(\operatorname{markedTranslation}\left(K, t\right), \operatorname{markedE}\left(K, a, b\right)\right)) \land (\operatorname{Commute}\left(\operatorname{markedTranslation}\left(K, t\right), \operatorname{markedF}\left(K, a, b\right)\right))))))) \land ((\operatorname{Sl2Relations}\left(\operatorname{h}\left(K, a, b\right), \operatorname{e}\left(K, a, b\right), \operatorname{f}\left(K, a, b\right)\right)) \land ((\operatorname{f}\left(K, a, b\right) = \operatorname{F3}\left(K, a, b\right)) \land (((\forall t \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{Commute}\left(\operatorname{translation}\left(K, t\right), \operatorname{h}\left(K, a, b\right)\right)) \land ((\operatorname{Commute}\left(\operatorname{translation}\left(K, t\right), \operatorname{e}\left(K, a, b\right)\right)) \land (\operatorname{Commute}\left(\operatorname{translation}\left(K, t\right), \operatorname{f}\left(K, a, b\right)\right)))) \land ((\operatorname{Commute}\left(\operatorname{U}\left(K, a, b\right), \operatorname{h}\left(K, a, b\right)\right)) \land ((\operatorname{Commute}\left(\operatorname{U}\left(K, a, b\right), \operatorname{e}\left(K, a, b\right)\right)) \land (\operatorname{Commute}\left(\operatorname{U}\left(K, a, b\right), \operatorname{f}\left(K, a, b\right)\right))))) \land (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; (\operatorname{h}\left(K, a, b\right)\left(\operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\right) = (\operatorname{cast}\left(\operatorname{integerWeight}\left(c\right), K\right)) \cdot (\operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right))) \land ((\operatorname{e}\left(K, a, b\right)\left(\operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\right) = \sum_{j\in\operatorname{Fin}\left(\operatorname{m}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{m}\left(c\right)\right)\right) = \operatorname{false}) \land (\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{m}\left(c\right)\right)\right) = \operatorname{true})), ((\operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right)) \cdot (\operatorname{cast}\left(\operatorname{m}\left(c\right), K\right) - \operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right))) \cdot (\operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(\operatorname{leftMove}\left(c, j\right)\right)\right)\right)), 0\right)) + \sum_{j\in\operatorname{Fin}\left(\operatorname{n}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{n}\left(c\right)\right)\right) = \operatorname{false}) \land (\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{n}\left(c\right)\right)\right) = \operatorname{true})), ((\operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right)) \cdot (\operatorname{cast}\left(\operatorname{n}\left(c\right), K\right) - \operatorname{cast}\left(\operatorname{val}\left(j\right) + 1, K\right))) \cdot (\operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(\operatorname{rightMove}\left(c, j\right)\right)\right)\right)), 0\right))) \land (\operatorname{f}\left(K, a, b\right)\left(\operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\right) = \sum_{j\in\operatorname{Fin}\left(\operatorname{m}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{m}\left(c\right)\right)\right) = \operatorname{true}) \land (\operatorname{u}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{m}\left(c\right)\right)\right) = \operatorname{false})), \operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(\operatorname{leftMove}\left(c, j\right)\right)\right)\right), 0\right)) + \sum_{j\in\operatorname{Fin}\left(\operatorname{n}\left(c\right) - 1\right)} (\operatorname{ifThenElse}\left(((\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right), \operatorname{n}\left(c\right)\right)\right) = \operatorname{true}) \land (\operatorname{v}\left(c\right)\left(\operatorname{finMk}\left(\operatorname{val}\left(j\right) + 1, \operatorname{n}\left(c\right)\right)\right) = \operatorname{false})), \operatorname{delta}\left(K, \operatorname{word}\left(\operatorname{encode}\left(\operatorname{rightMove}\left(c, j\right)\right)\right)\right), 0\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TwoWallSl2.literal_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed the coordinate delta basis injectively into the direct sum of the two-bin tensor spaces indexed by position and both lengths. The local swaps preserve filling. Their rational delta coefficients agree with the scalar extension in BinaryBinBaseChange, so the embedding intertwines all three endomorphisms. The supplied two-bin relations therefore hold on the marked space. Exchanging arcs exchanges the two summands of each action; translation changes only p. Thus all three operators commute with mark exchange and marked translation. The identities QS=2id and SQ=id+Jstar imply that S is injective, Jstar fixes its image, and S intertwines each descended action with its marked action. They transfer the commutator relations and translation symmetry to literal words. For the physical identification, the two wall positions and both arc intervals partition the cyclic sites. Bonds touching a wall contribute zero to F3. Every other bond belongs to exactly one arc interior, where encoding intertwines its swap with the cyclic site swap. Reindexing the complete bond sum gives f=F3, including the wraparound and empty-arc cases. The two marked lifts give identical basis images, and the inverse of two removes their duplication. Finally, weight_eq_level identifies the diagonal scalar with the integer inversion weight.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.e`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.f`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.h`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.integerWeight`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.leftMove`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.literal_action`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.markedE`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.markedF`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.markedH`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallSl2.rightMove`
- Dependency: [D5/S3/Quantum/SpinChains/TwoWallMarked](TwoWallMarked.md)
