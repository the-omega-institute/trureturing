# OrdinaryWords

## Abstract

Ternary ordinary gaps are counted by distributing ones and choosing insertion slots for isolated twos.

**Definition 1.1 (d I).**

$$\forall (n k : \mathbb{N}) , \operatorname{dI} n k = \operatorname{Nat}.\operatorname{card} \{f : \operatorname{Fin} n \to \operatorname{Fin} 3 \mid \operatorname{IsItalian} f \land (\sum_{i : \operatorname{Fin} n} (f i) . \operatorname{val}) = k\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.dI` (`✓ std3`).

*Citation.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Shao and Zhao, Definition 1.1 (p. 3): "where d_I(G, k) counts the Italian dominating functions of weight k." Definition 2.1 (p. 5): "The weight of f is ω(f) = Σ_{v∈V} f(v)." The vertices are Fin n and their labels are Fin 3. IsItalian uses finRotate n and its inverse for the cyclic neighbours. The count distinguishes all labelled maps, including their rotated or reflected copies.

**Definition 1.2 (Is Deficit).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) , \operatorname{IsDeficit} y = \forall i , y i = 2 \to (y ((\operatorname{finRotate} n) . \operatorname{symm} i)) . \operatorname{val} + (y (\operatorname{finRotate} n i)) . \operatorname{val} \leq 2$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.IsDeficit` (`✓ std3`).

*Citation.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Shao and Zhao, Corollary 3.2 (p. 7): "For the cycle C_n (n ≥ 3), a vector y ∈ {0,1,2}^n corresponds to an IDF of weight 2n−j if and only if ∑_{i=1}^n y_i=j and y_i = 2 ⟹ y_{i-1} + y_{i+1} ≤ 2 (indices modulo n)." This predicate states the local inequality; the sum condition is imposed separately.

**Theorem 1.3 (d I eq deficit card).**

$$\forall (n j : \mathbb{N}) , (j \leq 2 * n) \to \operatorname{dI} n (2 * n - j) = \operatorname{Nat}.\operatorname{card} \{y : \operatorname{Fin} n \to \operatorname{Fin} 3 \mid \operatorname{IsDeficit} y \land (\sum_{i : \operatorname{Fin} n} (y i) . \operatorname{val}) = j\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.dI_eq_deficit_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Complementing the labels identifies Italian functions of weight 2n−j with valid deficit maps of sum j.

**Theorem 1.4 (deficit valid iff).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) , \operatorname{IsDeficit} y \iff \forall i , y i = 2 \to (y ((\operatorname{finRotate} n) . \operatorname{symm} i) = 2 \to y (\operatorname{finRotate} n i) = 0) \land (y (\operatorname{finRotate} n i) = 2 \to y ((\operatorname{finRotate} n) . \operatorname{symm} i) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.deficit_valid_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

At a label two, another two on either side forces a zero on the opposite side.

**Definition 1.5 (label Count).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) (v : \operatorname{Fin} 3) , \operatorname{labelCount} y v = (\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} \operatorname{fun} i \mapsto y i = v) . \operatorname{card}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.labelCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Count the vertices with the specified label.

**Theorem 1.6 (shift valid iff).**

$$\forall (n : \mathbb{N}) [\operatorname{NeZero} n] (y : \operatorname{Fin} n \to \operatorname{Fin} 3) (k : \operatorname{Fin} n) , \operatorname{IsDeficit} ((\operatorname{fun} v \mapsto y (\operatorname{finCycle} k v))) \iff \operatorname{IsDeficit} y$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.shift_valid_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Cyclic reindexing preserves the local deficit inequalities.

**Theorem 1.7 (label Count shift).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) (k : \operatorname{Fin} n) (v : \operatorname{Fin} 3) , \operatorname{labelCount} ((\operatorname{fun} v \mapsto y (\operatorname{finCycle} k v))) v = \operatorname{labelCount} y v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.labelCount_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

A cyclic permutation preserves each label multiplicity.

**Theorem 1.8 (marked vertex identity).**

$$\forall (n : \mathbb{N}) [\operatorname{NeZero} n] (P : (\operatorname{Fin} n \to \operatorname{Fin} 3) \to \operatorname{Prop}) (v : \operatorname{Fin} 3) (m : \mathbb{N}) , (\forall y k , P ((\operatorname{fun} v \mapsto y (\operatorname{finCycle} k v))) \iff P y) \to (\forall y , P y \to \operatorname{labelCount} y v = m) \to m * \operatorname{Nat}.\operatorname{card} \{y : \operatorname{Fin} n \to \operatorname{Fin} 3 \mid P y\} = n * \operatorname{Nat}.\operatorname{card} \{y : \operatorname{Fin} n \to \operatorname{Fin} 3 \mid P y \land y 0 = v\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.marked_vertex_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Double counting pairs of a word and a vertex with label v yields the marked-vertex identity. The count uses all vertices even when a word is periodic.

**Definition 1.9 (double Two Count).**

$$\forall (n : \mathbb{N}) (y : \operatorname{Fin} n \to \operatorname{Fin} 3) , \operatorname{doubleTwoCount} y = (\operatorname{Finset}.\operatorname{univ}.\operatorname{filter} \operatorname{fun} i \mapsto y i = 2 \land y (\operatorname{finRotate} n i) = 2) . \operatorname{card}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.doubleTwoCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Count directed cyclic edges whose two endpoint labels are both two.

**Theorem 1.10 (double Two Count shift).**

$$\forall (n : \mathbb{N}) [\operatorname{NeZero} n] (y : \operatorname{Fin} n \to \operatorname{Fin} 3) (k : \operatorname{Fin} n) , \operatorname{doubleTwoCount} ((\operatorname{fun} v \mapsto y (\operatorname{finCycle} k v))) = \operatorname{doubleTwoCount} y$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.doubleTwoCount_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Cyclic reindexing preserves the number of consecutive pairs of twos.

**Definition 1.11 (Line OK).**

$$(\forall (p : \operatorname{Fin} 3) , \operatorname{LineOK} p [] \iff \operatorname{True}) \land (\forall (p x : \operatorname{Fin} 3) (\operatorname{xs} : \operatorname{List} (\operatorname{Fin} 3)) , \operatorname{LineOK} p (x :: \operatorname{xs}) \iff (x = 2 \to p . \operatorname{val} + (\operatorname{xs} . \operatorname{headD} 0) . \operatorname{val} \leq 2) \land \operatorname{LineOK} x \operatorname{xs})$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.LineOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The empty list satisfies the predicate. At a nonempty list, a leading two imposes the displayed inequality on its two neighbours, and the same test is applied recursively to the tail.

**Theorem 1.12 (line OK gap iff).**

$$\forall (l : \operatorname{List} (\operatorname{Fin} 3)) , ((0 : \operatorname{Fin} 3) \neg \in l) \to \operatorname{LineOK} 0 l \iff l = [2 , 2] \lor (\operatorname{List}.\operatorname{IsChain} (\operatorname{fun} a b : \operatorname{Fin} 3 \mapsto a \neq 2 \lor b \neq 2) l)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.lineOK_gap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

A zero-free list satisfying the local deficit inequalities is either the exceptional pair of twos or a list with no adjacent twos.

**Theorem 1.13 (split On no separator).**

$$\forall (\alpha : \operatorname{Type}) [\operatorname{DecidableEq} \alpha] (\operatorname{sep} : \alpha) (l : \operatorname{List} \alpha) , \forall g \in l . \operatorname{splitOn} \operatorname{sep} , \operatorname{sep} \neg \in g$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.splitOn_no_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Every piece obtained by splitting a list at a separator omits that separator.

**Definition 1.14 (join Zero).**

$$\forall (\operatorname{gs} : \operatorname{List} (\operatorname{List} (\operatorname{Fin} 3))) , \operatorname{joinZero} \operatorname{gs} = (\operatorname{gs} . \operatorname{map} (\operatorname{fun} g \mapsto (0 : \operatorname{Fin} 3) :: g)) . \operatorname{flatten}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.joinZero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Prefix every gap by a zero, then concatenate the lists in order.

**Theorem 1.15 (join Zero eq).**

$$\forall (\operatorname{gs} : \operatorname{List} (\operatorname{List} (\operatorname{Fin} 3))) , (\operatorname{gs} \neq []) \to \operatorname{joinZero} \operatorname{gs} = 0 :: [0] . \operatorname{intercalate} \operatorname{gs}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.joinZero_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

For a nonempty gap list, prefixing each gap by zero equals a leading zero followed by the intercalated gaps.

**Theorem 1.16 (join Zero split).**

$$\forall (l : \operatorname{List} (\operatorname{Fin} 3)) , \operatorname{joinZero} (l . \operatorname{splitOn} 0) = 0 :: l$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.joinZero_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Splitting at zero and prefixing the resulting gaps reconstructs the original list after one leading zero.

**Theorem 1.17 (line OK intercalate).**

$$\forall (\operatorname{gs} : \operatorname{List} (\operatorname{List} (\operatorname{Fin} 3))) , \operatorname{LineOK} 0 ([0] . \operatorname{intercalate} \operatorname{gs}) \iff \forall g \in \operatorname{gs} , \operatorname{LineOK} 0 g$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.lineOK_intercalate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The local inequalities on a list separated by zeros hold exactly when they hold on each gap.

**Theorem 1.18 (chosen card).**

$$\forall (\alpha : \operatorname{Type}) [\operatorname{Fintype} \alpha] [\operatorname{DecidableEq} \alpha] (a : \mathbb{N}) , \operatorname{Nat}.\operatorname{card} (\operatorname{CoeSort}.\operatorname{coe} ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset} \alpha) . \operatorname{powersetCard} a)) = (\operatorname{Fintype}.\operatorname{card} \alpha) . \operatorname{choose} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.chosen_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The subsets of cardinality a of a finite carrier are counted by the corresponding binomial coefficient.

**Theorem 1.19 (residual card).**

$$\forall (m b : \mathbb{N}) (e : \operatorname{CoeSort}.\operatorname{coe} ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset} (\operatorname{Fin} m)) . \operatorname{powersetCard} b)) , \operatorname{Fintype}.\operatorname{card} (\operatorname{CoeSort}.\operatorname{coe} ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset} (\operatorname{Fin} m)) \setminus (e) . \operatorname{val})) = m - b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.residual_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Removing b selected positions from Fin m leaves m−b positions.

**Definition 1.20 (Ordinary Word).**

$$\operatorname{OrdinaryWord} = \{l : \operatorname{List} (\operatorname{Fin} 3) \mid (0 : \operatorname{Fin} 3) \neg \in l \land (\operatorname{List}.\operatorname{IsChain} (\operatorname{fun} a b : \operatorname{Fin} 3 \mapsto a \neq 2 \lor b \neq 2) l)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.OrdinaryWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

An ordinary word is a zero-free ternary list in which two labels equal to two never occur consecutively.

**Definition 1.21 (Ordinary Family).**

$$\forall (\alpha : \operatorname{Type}) [\operatorname{Fintype} \alpha] (c a : \mathbb{N}) , \operatorname{OrdinaryFamily} \alpha c a = \{\operatorname{ls} : \alpha \to \operatorname{OrdinaryWord} \mid (\sum_{i} (\operatorname{ls} i) . \operatorname{val} . \operatorname{count} 1) = c \land (\sum_{i} (\operatorname{ls} i) . \operatorname{val} . \operatorname{count} 2) = a\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.OrdinaryFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

A family of ordinary words has c ones and a twos in total across its labelled index set.

**Theorem 1.22 (ordinary Family card).**

$$\forall (\alpha : \operatorname{Type}) [\operatorname{Fintype} \alpha] [\operatorname{DecidableEq} \alpha] (c a : \mathbb{N}) , \operatorname{Nat}.\operatorname{card} (\operatorname{OrdinaryFamily} \alpha c a) = (c + \operatorname{Fintype}.\operatorname{card} \alpha - 1) . \operatorname{choose} c * (c + \operatorname{Fintype}.\operatorname{card} \alpha) . \operatorname{choose} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ordinaryFamily_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Distribute c ones among the labelled ordinary words, then choose a of the c plus card α insertion slots. Inserting and deleting the twos are inverse constructions.

**Theorem 1.23 (ternary count length).**

$$\forall (l : \operatorname{List} (\operatorname{Fin} 3)) , l . \operatorname{count} 0 + l . \operatorname{count} 1 + l . \operatorname{count} 2 = l . \operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ternary_count_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The displayed identity relates ternary count length for the indicated parameters.

**Theorem 1.24 (ordinary length).**

$$\forall (l : \operatorname{OrdinaryWord}) , l . \operatorname{val} . \operatorname{count} 1 + l . \operatorname{val} . \operatorname{count} 2 = l . \operatorname{val} . \operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ordinary_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The ones and twos exhaust the entries of an ordinary word.

**Theorem 1.25 (ordinary Word card).**

$$\forall (c a : \mathbb{N}) , \operatorname{Nat}.\operatorname{card} \{l : \operatorname{OrdinaryWord} \mid l . \operatorname{val} . \operatorname{count} 1 = c \land l . \operatorname{val} . \operatorname{count} 2 = a\} = (c + 1) . \operatorname{choose} a$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ordinaryWord_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The ordinary words with c ones and a twos correspond to choosing a of their c+1 insertion slots.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.IsDeficit`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.LineOK`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.OrdinaryFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.OrdinaryWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.chosen_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.dI`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.dI_eq_deficit_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.deficit_valid_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.doubleTwoCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.doubleTwoCount_shift`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.joinZero`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.joinZero_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.joinZero_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.labelCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.labelCount_shift`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.lineOK_gap_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.lineOK_intercalate`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.marked_vertex_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ordinaryFamily_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ordinaryWord_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ordinary_length`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.residual_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.shift_valid_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.splitOn_no_separator`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords.ternary_count_length`
- Dependency: [D5/S3/Combinatorics/ArrowWilfGapData](../../ArrowWilfGapData.md)
- Dependency: [D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence](../CycleItalianDominationRecurrence.md)
