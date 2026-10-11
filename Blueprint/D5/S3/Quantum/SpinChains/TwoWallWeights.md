# Weight drops and nilpotence for two-wall words

## Abstract

Integer inversion weights control the exact local bond moves and the nilpotence of the literal two-wall action.

Let a,b be natural numbers. Literal words contain a ones, b twos and two walls on the cyclic sites Pos(a,b). The binary coordinates between the walls use true for two and false for one. The operator h and its integer coordinate weight are those of TwoWallSl2. In F(K,a,b,i), the indices 0,1,2 denote the physical operators F1,F2,F3, with input pairs 32,13,21 respectively. All operator statements below hold over every field K of characteristic zero. Submodule inequalities denote inclusion.

**Definition 1.1 (The weight of a literal word).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{wordWeight}\left(w\right) = \operatorname{integerWeight}\left(\operatorname{decode}\left((w, \operatorname{choose}\left(\left\{p \mid p \in \operatorname{Pos}\left(a, b\right) \land (w\left(p\right) = \operatorname{wall})\right\}\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallWeights.wordWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose a wall of w by classical choice, mark it, decode the two arcs and apply integerWeight. The set supplied to choose consists of the sites carrying a wall and is nonempty because there are exactly two walls. The tuple in the formula is regarded as a marked word; its wall certificate is implicit. The coordinate identity below shows that the result agrees with integerWeight for every marking.

**Theorem 1.2 (Integral weights and their bounds).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{wordWeight}\left(\operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right) = \operatorname{integerWeight}\left(c\right)) \land ((\forall w \in \operatorname{Word}\left(a, b\right),\; \operatorname{h}\left(K, a, b\right)\left(\operatorname{delta}\left(K, w\right)\right) = (\operatorname{cast}\left(\operatorname{wordWeight}\left(w\right), K\right)) \cdot (\operatorname{delta}\left(K, w\right))) \land ((\operatorname{IntegralWeights}\left(\operatorname{h}\left(K, a, b\right)\right)) \land (\forall w \in \operatorname{Word}\left(a, b\right),\; (-((a) \cdot (b)) \le \operatorname{wordWeight}\left(w\right)) \land (\operatorname{wordWeight}\left(w\right) \le (a) \cdot (b)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TwoWallWeights.weight_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate delta formula identifies the chosen integer weight with the eigenvalue of h, independently of the chosen wall. For an arc of length m with r twos, its inversion count lies between zero and r(m−r); hence its weight lies between −r(m−r) and r(m−r). Adding the two arc bounds and the nonnegative cross terms gives the interval [−ab,ab]. The finite image of wordWeight on all literal words supplies an integral weight set whose eigenspaces span the whole space.

**Theorem 1.3 (Exact bond drops, filtration descent and nilpotence).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\forall w \in \operatorname{Word}\left(a, b\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{Allowed}\left(0, w, p\right)) \Rightarrow (\operatorname{wordWeight}\left(\operatorname{swapWord}\left(p, w\right)\right) = \operatorname{wordWeight}\left(w\right) - a)) \land ((\forall w \in \operatorname{Word}\left(a, b\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{Allowed}\left(1, w, p\right)) \Rightarrow (\operatorname{wordWeight}\left(\operatorname{swapWord}\left(p, w\right)\right) = \operatorname{wordWeight}\left(w\right) - b)) \land ((\forall w \in \operatorname{Word}\left(a, b\right),\; \forall p \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{Allowed}\left(2, w, p\right)) \Rightarrow (\operatorname{wordWeight}\left(\operatorname{swapWord}\left(p, w\right)\right) = \operatorname{wordWeight}\left(w\right) - 2)) \land (((2 \le a) \Rightarrow ((2 \le b) \Rightarrow ((\forall i \in \operatorname{Fin}\left(3\right),\; \forall s \in \mathbb{Z},\; \operatorname{map}\left(\operatorname{weightLE}\left(\operatorname{h}\left(K, a, b\right), s\right), \operatorname{F}\left(K, a, b, i\right)\right) \le \operatorname{weightLE}\left(\operatorname{h}\left(K, a, b\right), s - 2\right)) \land ((\forall x \in (\operatorname{Fin}\left(3\right) \to K),\; \forall s \in \mathbb{Z},\; \operatorname{map}\left(\operatorname{weightLE}\left(\operatorname{h}\left(K, a, b\right), s\right), \operatorname{T}\left(K, a, b, x\right)\right) \le \operatorname{weightLE}\left(\operatorname{h}\left(K, a, b\right), s - 2\right)) \land (\forall x \in (\operatorname{Fin}\left(3\right) \to K),\; (\operatorname{T}\left(K, a, b, x\right))^{(a) \cdot (b) + 1} = 0))))) \land ((\operatorname{F3}\left(K, a, b\right))^{(a) \cdot (b) + 1} = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TwoWallWeights.weight_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the contribution of a binary arc B as chi(B)=2 level(B)−ones(B)(length(B)−ones(B)). Prepending a two adds the number of ones in B, and appending a two subtracts it. Prepending a one subtracts the number of twos, and appending a one adds it. For 32 to 23, mark the wall in the source and move the initial two from the first arc to the end of the second arc; the two changes add to −a. The reverse wall move with a one yields the 13 to 31 change −b. Inside either arc, 21 to 12 removes one inversion and gives −2; equivalently the same drop follows from the h,F3 commutator and the positive delta coefficient of an enabled bond. When a,b are at least two, every term in every bond sum drops weight by at least two. The delta basis description of weightLE extends this to all vectors and every linear combination T. After ab+1 steps the top possible weight ab is sent strictly below −ab, where the filtration is zero. The F3 conclusion holds for every a,b, including zero and one.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWeights.weight_control`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWeights.weight_structure`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallWeights.wordWeight`
- Dependency: [D5/S3/Quantum/SpinChains/TwoWallSl2](TwoWallSl2.md)
