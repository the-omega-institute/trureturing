# GenericLieLengthFiltration

## Abstract

Right-nested words, their length filtration and dimension estimates.

**Definition 1.1 (suSet).**

$$\forall (n : \mathbb{N}) (X : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , X \in \operatorname{suSet} n \iff (\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right) = - X \land \operatorname{Matrix} . \operatorname{trace} X = 0)$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suSet` (`✓ std3`).

*Citation.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Commentary.*

The real submodule consists of skew-Hermitian matrices with zero trace.

**Definition 1.2 (suLie).**

$$\forall (n : \mathbb{N}) (X : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , X \in \operatorname{suLie} n \iff X \in \operatorname{suSet} n$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suLie` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same carrier is a real Lie subalgebra with the matrix commutator.

**Definition 1.3 (layer).**

$$\begin{aligned}\forall (n : \mathbb{N}) (S : \operatorname{Finset} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{layer} S 0 = \operatorname{Bot}.\operatorname{bot}\\\forall (n : \mathbb{N}) (S : \operatorname{Finset} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{layer} S 1 = \operatorname{Submodule} . \operatorname{span} \mathbb{R} (S : \operatorname{Set} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))\\\forall (n k : \mathbb{N}) (S : \operatorname{Finset} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{layer} S (k + 2) = \operatorname{Submodule} . \operatorname{span} \mathbb{R} \{ Z : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C} \mid \exists (X : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , X \in S \land \exists (Y : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , Y \in \operatorname{layer} S (k + 1) \land Z = [ X , Y ] \}\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.layer` (`✓ std3`).

*Citation.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Commentary.*

Definition 3 (arXiv:2301.08241v3, p. 17) defines the layers by “U₁ = span{U}; Uₙ = span[U,Uₙ₋₁], n ≥ 2.” The zero layer is bottom, and the positive layers have exactly the source recurrence.

**Definition 1.4 (lieLength).**

$$\forall (n : \mathbb{N}) (S : \operatorname{Finset} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{lieLength} n S = \operatorname{sInf} \{ l : \mathbb{N} \mid 1 \leq l \land (\operatorname{iSup}_{k:\mathbb{N}\in\operatorname{Finset} . \operatorname{Icc} 1 l} \operatorname{layer} S k) = \operatorname{suSet} n \}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.lieLength` (`✓ std3`).

*Citation.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Commentary.*

Definition 3 (arXiv:2301.08241v3, p. 17): “The Lie-length of a Lie-generating system U of a finite-dimensional Lie-algebra A is the minimal length of the (right-nested) brackets such that the brackets span the whole Lie-algebra, namely Lieℓ(U)=min{ℓ | A=span{Uₙ, n≤ℓ}}, where Uₙ is defined as: U₁=span{U}; Uₙ=span[U,Uₙ₋₁], n≥2.” Natural sInf returns zero for an empty set; the asserted bounds apply to samples for which the layers span suSet.

**Definition 1.5 (suCoordinateMap).**

$$\forall (g n : \mathbb{N}) (x : \operatorname{Fin} g \to \operatorname{Fin} (\operatorname{Module} . \operatorname{finrank} \mathbb{R} (\operatorname{suSet} n)) \to \mathbb{R}) (j : \operatorname{Fin} g) , \operatorname{suCoordinateMap} g n x j = \operatorname{Subtype} . \operatorname{val} ((\operatorname{Module} . \operatorname{finBasis} \mathbb{R} (\operatorname{suSet} n)) . \operatorname{equivFun} . \operatorname{symm} (x j))$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suCoordinateMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Module.finBasis supplies real coordinates for the traceless skew-Hermitian submodule. The map sends each generator coordinate vector through the inverse basis equivalence.

**Definition 1.6 (suPairMeasure).**

$$\forall (g n : \mathbb{N}) , \operatorname{suPairMeasure} g n = \operatorname{MeasureTheory} . \operatorname{Measure} . \operatorname{map} (\operatorname{suCoordinateMap} g n) \operatorname{volume}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suPairMeasure` (`✓ std3`).

*Citation.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Commentary.*

The measure is the pushforward of real coordinate Lebesgue measure. Matrices use their entries as functions Fin n → Fin n → ℂ. Almost everywhere therefore means outside a Lebesgue null set of generator coordinates.

**Definition 1.7 (RightWord).**

$$\begin{aligned}\forall (I : \operatorname{Type} *) , \operatorname{RightWord} . \operatorname{single} : I \to \operatorname{RightWord} I\\\forall (I : \operatorname{Type} *) , \operatorname{RightWord} . \operatorname{cons} : I \to \operatorname{RightWord} I \to \operatorname{RightWord} I\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.RightWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RightWord is the inductive type with precisely the single and cons constructors. It represents nonempty right-nested brackets.

**Definition 1.8 (rightWordLength).**

$$\begin{aligned}\forall (I : \operatorname{Type} *) (i : I) , \operatorname{rightWordLength} (\operatorname{RightWord} . \operatorname{single} i) = 1\\\forall (I : \operatorname{Type} *) (i : I) (w : \operatorname{RightWord} I) , \operatorname{rightWordLength} (\operatorname{RightWord} . \operatorname{cons} i w) = \operatorname{rightWordLength} w + 1\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightWordLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Length counts generator letters.

**Definition 1.9 (rightWordEval).**

$$\begin{aligned}\forall (I M : \operatorname{Type} *) [ \operatorname{LieRing} M ] (S : I \to M) (i : I) , \operatorname{rightWordEval} S (\operatorname{RightWord} . \operatorname{single} i) = S i\\\forall (I M : \operatorname{Type} *) [ \operatorname{LieRing} M ] (S : I \to M) (i : I) (w : \operatorname{RightWord} I) , \operatorname{rightWordEval} S (\operatorname{RightWord} . \operatorname{cons} i w) = [ S i , \operatorname{rightWordEval} S w ]\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightWordEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation uses the right-nested Lie bracket.

**Definition 1.10 (rightSpan).**

$$\forall (I K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (S : I \to M) (L : \mathbb{N}) , \operatorname{rightSpan} (K := K) S L = \operatorname{Submodule} . \operatorname{span} K \{ x : M \mid \exists (w : \operatorname{RightWord} I) , w . \operatorname{rightWordLength} \leq L \land \operatorname{rightWordEval} S w = x \}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The submodule is spanned by evaluations of words of length at most L.

**Theorem 1.11 (word_mem).**

$$\forall (I K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (S : I \to M) (w : \operatorname{RightWord} I) (L : \mathbb{N}) , w . \operatorname{rightWordLength} \leq L \to \operatorname{rightWordEval} S w \in \operatorname{rightSpan} (K := K) S L$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.word_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each sufficiently short word belongs to the defining span.

**Theorem 1.12 (rightSpan_mono).**

$$\forall (I K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (S : I \to M) (a b : \mathbb{N}) , a \leq b \to \operatorname{rightSpan} (K := K) S a \leq \operatorname{rightSpan} (K := K) S b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the length cutoff enlarges the span.

**Theorem 1.13 (word_bracket_mem).**

$$\forall (I K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (S : I \to M) (u v : \operatorname{RightWord} I) , [ \operatorname{rightWordEval} S u , \operatorname{rightWordEval} S v ] \in \operatorname{rightSpan} (K := K) S (u . \operatorname{rightWordLength} + v . \operatorname{rightWordLength})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.word_bracket_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Jacobi induction moves brackets into the right-nested filtration and adds the two lengths.

**Theorem 1.14 (rightSpan_bracket_mem).**

$$\forall (I K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (S : I \to M) (r t : \mathbb{N}) (x y : M) , x \in \operatorname{rightSpan} (K := K) S r \to y \in \operatorname{rightSpan} (K := K) S t \to [ x , y ] \in \operatorname{rightSpan} (K := K) S (r + t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_bracket_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bilinearity extends the word estimate to both spans.

**Theorem 1.15 (polynomial_ad_mem).**

$$\forall (I K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (S : I \to M) (i : I) (L : \mathbb{N}) (x : M) (p : \operatorname{Polynomial} K) , x \in \operatorname{rightSpan} (K := K) S L \to \operatorname{Polynomial} . \operatorname{aeval} (\operatorname{LieAlgebra} . \operatorname{ad} K M (S i)) p x \in \operatorname{rightSpan} (K := K) S (L + p . \operatorname{natDegree})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.polynomial_ad_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A polynomial in the generator adjoint increases the length by at most its natural degree.

**Theorem 1.16 (rightSpan_real_le_su).**

$$\forall (I : \operatorname{Type} *) (n : \mathbb{N}) (S : I \to \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) (L : \mathbb{N}) , (\forall (i : I) , S i \in \operatorname{suSet} n) \to \operatorname{rightSpan} (K := \mathbb{R}) S L \leq \operatorname{suSet} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_real_le_su` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Skew-Hermitian trace-zero generators stay in the same submodule under real linear combinations and brackets.

**Theorem 1.17 (rightSpan_complex_to_real).**

$$\forall (I : \operatorname{Type} *) (n : \mathbb{N}) (S : I \to \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) (L : \mathbb{N}) (X : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , (\forall (i : I) , S i \in \operatorname{suSet} n) \to X \in \operatorname{suSet} n \to X \in \operatorname{rightSpan} (K := \mathbb{C}) S L \to X \in \operatorname{rightSpan} (K := \mathbb{R}) S L$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_complex_to_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The skew-adjoint projection replaces every complex coefficient by its real part on a skew-Hermitian word. Complex spanning therefore transfers to the real form.

**Theorem 1.18 (rightSpan_reindex_le).**

$$\forall (I J K M : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] (f : I \to J) (S : I \to M) (T : J \to M) (L : \mathbb{N}) , (\forall (i : I) , T (f i) = S i) \to \operatorname{rightSpan} (K := K) S L \leq \operatorname{rightSpan} (K := K) T L$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_reindex_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Relabeling generator indices preserves evaluations and word lengths.

**Theorem 1.19 (lieLength_le_of_span).**

$$\forall (g n L : \mathbb{N}) (S : \operatorname{Fin} g \to \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , 1 \leq L \to \operatorname{rightSpan} (K := \mathbb{R}) S L = \operatorname{suSet} n \to \operatorname{lieLength} n (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} S) \leq L$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.lieLength_le_of_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cumulative source layers equal the bounded-word span, so saturation bounds the source Lie-length.

**Definition 1.20 (words).**

$$\begin{aligned}\forall (g : \mathbb{N}) , \operatorname{words} g 0 = \emptyset\\\forall (g L : \mathbb{N}) , \operatorname{words} g (L + 1) = \operatorname{Finset} . \operatorname{univ} . \operatorname{image} \operatorname{RightWord} . \operatorname{single} \cup \operatorname{Finset} . \operatorname{univ} . \operatorname{biUnion} (\operatorname{fun} (i : \operatorname{Fin} g) \mapsto (\operatorname{words} g L) . \operatorname{image} (\operatorname{RightWord} . \operatorname{cons} i))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.words` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite enumeration consists of single letters and words formed by prepending a letter.

**Definition 1.21 (wordBudget).**

$$\begin{aligned}\forall (g : \mathbb{N}) , \operatorname{wordBudget} g 0 = 0\\\forall (g L : \mathbb{N}) , \operatorname{wordBudget} g (L + 1) = g + g * \operatorname{wordBudget} g L\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.wordBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recurrence equals the sum of g to powers 1 through L.

**Theorem 1.22 (card_words_le).**

$$\forall (g L : \mathbb{N}) , (\operatorname{words} g L) . \operatorname{card} \leq \operatorname{wordBudget} g L$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.card_words_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Union and image cardinalities bound the number of enumerated words.

**Theorem 1.23 (lower_lieLength_of_saturation).**

$$\forall (n g L : \mathbb{N}) (S : \operatorname{Fin} g \to \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , 2 \leq n \to 2 \leq g \to 1 \leq L \to \operatorname{rightSpan} (K := \mathbb{R}) S L = \operatorname{suSet} n \to (1 / \operatorname{Real} . \operatorname{log} ((g : \mathbb{R}) + 1)) * \operatorname{Real} . \operatorname{log} (n : \mathbb{R}) \leq (\operatorname{lieLength} n (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} S) : \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.lower_lieLength_of_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real dimension n² − 1 cannot exceed the number of words. Bounding the word budget by (g + 1) to the cutoff yields this logarithmic lower bound.

**Theorem 1.24 (upper_log).**

$$\forall (n : \mathbb{N}) , (16 * (1 + \operatorname{Nat} . \operatorname{log} 2 (n + 1)) : \mathbb{R}) \leq (32 / \operatorname{Real} . \operatorname{log} 2) * \operatorname{Real} . \operatorname{log} ((n : \mathbb{R}) + 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.upper_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nat.log 2 is the integer base-two logarithm. The cast encloses the natural expression on the left; the right-hand logarithm is real.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.RightWord`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.card_words_le`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.layer`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.lieLength`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.lieLength_le_of_span`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.lower_lieLength_of_saturation`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.polynomial_ad_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_bracket_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_complex_to_real`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_mono`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_real_le_su`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightSpan_reindex_le`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightWordEval`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.rightWordLength`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suCoordinateMap`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suLie`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suPairMeasure`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.suSet`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.upper_log`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.wordBudget`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.word_bracket_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.word_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthFiltration.words`
