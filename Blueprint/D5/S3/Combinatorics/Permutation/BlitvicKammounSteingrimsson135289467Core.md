# BlitvicKammounSteingrimsson135289467Core

## Abstract

Symbolic order relations and cardinalities for the 135289467 packing count.

**Definition 1.1 (pattern).**

$$pattern = (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ])$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.pattern` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The one-line pattern 135289467 with positions and ranks decreased by one.

**Definition 1.2 (inversePattern).**

$$inversePattern = (! [ 0 , 3 , 1 , 6 , 2 , 7 , 8 , 4 , 5 ])$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.inversePattern` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The inverse-pattern order is 1,4,2,7,3,8,9,5,6 in one-based notation.

**Theorem 1.3 (packing chain iff).**

$$\forall (j : \mathbb{N}) , \forall (w : Fin (9 + (j - 1) \cdot 6) \to Fin (9 + (j - 1) \cdot 6)) , Packs pattern 3 j w \iff \forall t : Fin j , StrictMono (a : Fin 9 \mapsto w (windowIndex 9 3 j t (inversePattern a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.packing_chain_iff` (`✓ std3`). ∎

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Each prescribed occurrence is equivalent to strict increase in the inverse-pattern order.

**Theorem 1.4 (first count).**

$$count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 1 = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.first_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

A single prescribed occurrence has exactly one permutation.

**Definition 1.5 (C).**

$$\forall (\alpha : Type) [ LinearOrder \alpha ] , \forall (t : \mathbb{N}) , \forall (f : \mathbb{N} \to \alpha) , C t f = (f (6 \cdot t) < f (6 \cdot t + 3) \land f (6 \cdot t + 3) < f (6 \cdot t + 1) \land f (6 \cdot t + 1) < f (6 \cdot t + 6) \land f (6 \cdot t + 6) < f (6 \cdot t + 2) \land f (6 \cdot t + 2) < f (6 \cdot t + 7) \land f (6 \cdot t + 7) < f (6 \cdot t + 8) \land f (6 \cdot t + 8) < f (6 \cdot t + 4) \land f (6 \cdot t + 4) < f (6 \cdot t + 5))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.C` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The nine entries of a window increase in inverse-pattern order.

**Definition 1.6 (Q).**

$$\forall (\alpha : Type) [ LinearOrder \alpha ] , \forall (j : \mathbb{N}) , \forall (f : \mathbb{N} \to \alpha) , Q j f = ((f 8 < f 4 \land f 4 < f 5) \land (f 12 < f 8 \land f 8 < f 13 \land f 13 < f 14 \land f 14 < f 10 \land f 10 < f 11) \land (\forall t , 2 \le t \to t < j \to C t f))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The residual comparisons consist of two fixed chains and every window chain from index two onwards.

**Definition 1.7 (QSupport).**

$$\forall (j : \mathbb{N}) , \forall (x : \mathbb{N}) , QSupport j x = (x = 4 \lor x = 5 \lor x = 8 \lor x = 10 \lor x = 11 \lor (12 \le x \land x \le 6 \cdot j + 2))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.QSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The residual labels are 4, 5, 8, 10, 11 and the interval from 12 through 6j+2.

**Definition 1.8 (Head).**

$$\forall (\alpha : Type) [ LinearOrder \alpha ] , \forall (f : \mathbb{N} \to \alpha) , Head f = (f 0 < f 3 \land f 3 < f 1 \land f 1 < f 6 \land f 6 < f 2 \land f 6 < f 9 \land f 2 < f 7 \land f 9 < f 7)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.Head` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The first seven removed labels have two possible linear orders, distinguished by 2 and 9.

**Theorem 1.9 (q min).**

$$\forall (\alpha : Type) [ LinearOrder \alpha ] , \forall (j : \mathbb{N}) , (2 \le j) \to (\forall (f : \mathbb{N} \to \alpha) , (Q j f) \to (\forall (x : \mathbb{N}) , (QSupport j x) \to (f 12 \le f x)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.q_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The label 12 precedes every residual label. Induction along the overlapping windows establishes the comparison.

**Theorem 1.10 (head iff).**

$$\forall (\alpha : Type) [ LinearOrder \alpha ] , \forall (j : \mathbb{N}) , (2 \le j) \to (\forall (f : \mathbb{N} \to \alpha) , (\forall t , t < j \to C t f) \iff Head f \land f 7 < f 12 \land Q j f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.head_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The full window order separates into the initial seven-label order, the comparison between 7 and 12, and the residual order.

**Definition 1.11 (word).**

$$\forall (n : \mathbb{N}) , \forall (w : \operatorname{Equiv} . \operatorname{Perm} (Fin n)) , word w = (\operatorname{List} . \operatorname{ofFn} (i \mapsto \operatorname{val}\left(w . \operatorname{symm} i\right)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The inverse permutation lists positions in increasing order of their ranks.

**Theorem 1.12 (word perm).**

$$\forall (n : \mathbb{N}) , \forall (w : \operatorname{Equiv} . \operatorname{Perm} (Fin n)) , (word w) . Perm (\operatorname{List} . \operatorname{range} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.word_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The inverse-rank word contains each label from zero to n minus one exactly once.

**Theorem 1.13 (word idxOf).**

$$\forall (n : \mathbb{N}) , \forall (w : \operatorname{Equiv} . \operatorname{Perm} (Fin n)) , \forall (i : Fin n) , (word w) . idxOf \operatorname{val}\left(i\right) = \operatorname{val}\left(w i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.word_idxOf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The index of a position in the inverse-rank word is its permutation rank.

**Definition 1.14 (keep).**

$$\forall (x : \mathbb{N}) , keep x = (decide (x \neq 4 \land x \neq 5))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.keep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The filter keeps every label except 4 and 5.

**Definition 1.15 (Shuffle).**

$$\forall (low : List \mathbb{N}) , \forall (high : List \mathbb{N}) , Shuffle low high = (\{ l : List \mathbb{N} // l . \operatorname{Perm} (\operatorname{List} . \operatorname{append} low high) \land l . \operatorname{filter} keep = low \land l . \operatorname{filter} (x \mapsto \operatorname{Bool} . \operatorname{not} (keep x)) = high \})$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.Shuffle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

A shuffle preserves the two filtered lists and has their combined multiset.

**Theorem 1.16 (shuffle card).**

$$\forall (low : List \mathbb{N}) , \forall (high : List \mathbb{N}) , (\forall x \in low , keep x = true) \to ((\forall x \in high , keep x = false) \to (\operatorname{Nat} . \operatorname{card} (Shuffle low high) = (low . \operatorname{length} + high . \operatorname{length}) . choose low . \operatorname{length}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.shuffle_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The number of shuffles is the binomial coefficient determined by the two list lengths.

**Theorem 1.17 (binomial factor).**

$$\forall (j : \mathbb{N}) , (3 \le j) \to (121 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 0 + 168 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 1 + 72 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 2 = (6 \cdot j - 7) ^ 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.binomial_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The polynomial in the source binomial basis equals the square of 6j minus 7.

**Theorem 1.18 (idxOf filter lt iff).**

$$\forall (p : \mathbb{N} \to Bool) , \forall (l : List \mathbb{N}) , \forall (a : \mathbb{N}) , \forall (b : \mathbb{N}) , (p a = true) \to ((p b = true) \to ((l . \operatorname{filter} p) . idxOf a < (l . \operatorname{filter} p) . idxOf b \iff l . \operatorname{idxOf} a < l . \operatorname{idxOf} b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.idxOf_filter_lt_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Filtering preserves and reflects the order of the first occurrences of two retained labels, including the case of absent labels.

**Theorem 1.19 (strip least).**

$$\forall (l : List \mathbb{N}) , \forall (L : List \mathbb{N}) , \forall (a : \mathbb{N}) , (l . \operatorname{Perm} (a :: L)) \to ((\forall x \in l , x \neq a \to l . \operatorname{idxOf} a < l . \operatorname{idxOf} x) \to (\exists r , l = a :: r \land r . \operatorname{Perm} L))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.strip_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

A label whose first occurrence precedes every other label must be the first entry; removing it preserves the remaining multiset.

**Theorem 1.20 (keep all).**

$$\forall (L : List \mathbb{N}) , (\operatorname{List} . \operatorname{Disjoint} L [ 12 , 15 , 8 , 13 , 4 , 5 ]) \to (\forall x \in L , keep x = true)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.keep_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The displayed statement gives the relation used in the packing count.

**Theorem 1.21 (one tail).**

$$\forall (L : List \mathbb{N}) , \forall (z : List \mathbb{N}) , (\operatorname{List} . \operatorname{Disjoint} L [ 12 , 15 , 8 , 13 , 4 , 5 ]) \to ((z . \operatorname{Perm} (13 :: 4 :: 5 :: L)) \to ((z . \operatorname{idxOf} 4 < z . \operatorname{idxOf} 5) \to ((\forall x \in L , z . \operatorname{idxOf} 13 < z . \operatorname{idxOf} x) \to (\exists r , r . \operatorname{Perm} L \land z . \operatorname{Perm} (\operatorname{List} . \operatorname{append} (13 :: r) [ 4 , 5 ]) \land z . \operatorname{filter} keep = 13 :: r \land z . \operatorname{filter} (x \mapsto \operatorname{Bool} . \operatorname{not} (keep x)) = [ 4 , 5 ]))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.one_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The tail following one marker is a shuffle of a survivor word beginning with 13 and the ordered pair 4,5.

**Definition 1.22 (labels).**

$$\forall (j : \mathbb{N}) , labels j = (\operatorname{List} . \operatorname{append} [ 4 , 5 , 8 , 10 , 11 ] (\operatorname{List} . \operatorname{range} ' 12 (6 \cdot j - 9)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.labels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The residual alphabet is an explicit five-label prefix followed by an interval.

**Definition 1.23 (words).**

$$\forall (j : \mathbb{N}) , words j = (\{ l \mid l . \operatorname{Perm} (labels j) \land Q j l . \operatorname{idxOf} \})$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.words` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Residual words permute the residual alphabet and satisfy its order comparisons.

**Theorem 1.24 (mem labels).**

$$\forall (j : \mathbb{N}) , (2 \le j) \to (\forall (x : \mathbb{N}) , x \in labels j \iff QSupport j x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.mem_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Membership in the residual alphabet is exactly the displayed support condition.

**Theorem 1.25 (labels nodup).**

$$\forall (j : \mathbb{N}) , (labels j) . Nodup$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.labels_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The residual alphabet has no repeated labels.

**Theorem 1.26 (words finite).**

$$\forall (j : \mathbb{N}) , (words j) . Finite$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.words_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

There are finitely many permutations of the residual alphabet.

**Theorem 1.27 (q congr).**

$$\forall (j : \mathbb{N}) , (2 \le j) \to (\forall (f : \mathbb{N} \to \mathbb{N}) , \forall (g : \mathbb{N} \to \mathbb{N}) , (\forall x y , QSupport j x \to QSupport j y \to (f x < f y \iff g x < g y)) \to (Q j f \iff Q j g))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.q_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The residual predicate depends only on pairwise comparisons between labels in its support.

**Theorem 1.28 (residual recurrence).**

$$\forall (j : \mathbb{N}) , (2 \le j) \to ((words (j + 1)) . ncard = (6 \cdot j - 1) ^ 2 \cdot (words j) . ncard)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.residual_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The next residual language has cardinality equal to the preceding one multiplied by the square of 6j minus 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.C`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.Head`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.Q`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.QSupport`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.Shuffle`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.binomial_factor`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.first_count`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.head_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.idxOf_filter_lt_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.inversePattern`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.keep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.keep_all`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.labels`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.labels_nodup`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.mem_labels`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.one_tail`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.packing_chain_iff`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.pattern`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.q_congr`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.q_min`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.residual_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.shuffle_card`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.strip_least`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.word`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.word_idxOf`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.word_perm`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.words`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core.words_finite`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery](../../Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.md)
- Dependency: [D5/S3/Combinatorics/Permutation/PackingMaximumRefutation](PackingMaximumRefutation.md)
- Dependency: [D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending](../RotationAvoidance/RotationAvoidanceAscending.md)
