# The sharp noncommutative Hunter inequality

## Abstract

The literal symmetrized word polynomial satisfies the sharp Garcia--Volcic operator bound, through a finite factorial Gram matrix and explicit inverse columns.

**Definition 1.1 (Word coefficients).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), \operatorname{coefficient}\left(w\right) = \frac{\prod_{i:\operatorname{Fin}\left(n\right)} ((\operatorname{Nat.factorial}\left(\operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(w\right)\right)\right):\mathbb{C}))}{(\operatorname{Nat.factorial}\left(k\right):\mathbb{C})}$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.coefficient` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

The coefficient is the reciprocal abelianization-fibre cardinality: the occupation-count formula gives k! divided by the product of multiplicity factorials. All words in one fibre receive the same coefficient.

**Definition 1.2 (Ordered evaluation).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall A:\operatorname{Type}, [\operatorname{Monoid}\left(A\right)] \forall X:\operatorname{Fin}\left(n\right) \to A, \forall w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), \operatorname{wordEval}\left(X, w\right) = \operatorname{List.prod}\left(\operatorname{List.ofFn}\left((j:\operatorname{Fin}\left(k\right)) \mapsto X\left(w\left(j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.wordEval` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

The word is evaluated in its written order using List.ofFn and List.prod. A monoid suffices; operator multiplication is composition.

**Definition 1.3 (The NCHS polynomial).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall A:\operatorname{Type}, [\operatorname{Ring}\left(A\right)] [\operatorname{Algebra}\left(\mathbb{C}, A\right)] \forall X:\operatorname{Fin}\left(n\right) \to A, \operatorname{nchs}\left(n, k, X\right) = \sum_{w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right)} ((\operatorname{coefficient}\left(w\right)) \cdot (\operatorname{wordEval}\left(X, w\right)))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.nchs` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Equation (3), page 2: “The noncommutative complete homogeneous symmetric (NCHS) polynomial of degree d in n (noncommuting) variables is” H_d(x_1,...,x_n) := sigma(h_d(x_1,...,x_n)). The displayed word sum is exactly this symmetrized lift, since each commutative monomial occurs once in h_d.

**Definition 1.4 (The literal sharp constant).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \operatorname{mu}\left(n, d\right) = \operatorname{ite}\left(n = 1, 1, \operatorname{ite}\left(\operatorname{Odd}\left(d\right), \frac{(\operatorname{Nat.choose}\left(n - 1 + 2 \cdot d, 2 \cdot d\right):\mathbb{R})}{(\operatorname{Nat.choose}\left(n - 1 + d, d\right):\mathbb{R}) \cdot \left((\operatorname{Nat.choose}\left(n - 1 + d, d\right):\mathbb{R}) + 1\right)}, \frac{(\operatorname{Nat.choose}\left(n - 1 + 2 \cdot d, 2 \cdot d\right):\mathbb{R})}{(\operatorname{Nat.choose}\left(n - 1 + d, d\right):\mathbb{R}) \cdot \left((\operatorname{Nat.choose}\left(n - 1 + d, d\right):\mathbb{R}) + (n:\mathbb{R}) - 1\right)}\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.mu` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Theorem 1.1(ii), pages 2--3. The n = 1 branch is retained. Natural subtraction is truncated; division in this formula is real field division.

**Definition 1.5 (The Hunter residual).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall X:\operatorname{Fin}\left(n\right) \to \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right), \operatorname{residual}\left(n, d, X\right) = \operatorname{nchs}\left(n, 2 \cdot d, X\right) - ((\operatorname{mu}\left(n, d\right):\mathbb{C})) \cdot (\sum_{i:\operatorname{Fin}\left(n\right)} (X\left(i\right)^{2 \cdot d}))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.residual` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

The residual is the literal difference of H_{2d} and the sharp multiple of the sum of even powers.

**Definition 1.6 (The word Gram matrix).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \operatorname{gram}\left(n, d\right) = (u:\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(n\right)) \mapsto (v:\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(n\right)) \mapsto \frac{\prod_{i:\operatorname{Fin}\left(n\right)} ((\operatorname{Nat.factorial}\left(\operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(u\right)\right) + \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(v\right)\right)\right):\mathbb{C}))}{(\operatorname{Nat.factorial}\left(2 \cdot d\right):\mathbb{C})}$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.gram` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Equation (5), page 3, uses the reciprocal fibre size of the abelianized concatenation of the reversed first word and the second word.

**Definition 1.7 (Pure words).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \forall w:\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(n\right), \operatorname{pure}\left(w\right) \Leftrightarrow \exists i:\operatorname{Fin}\left(n\right), \forall j:\operatorname{Fin}\left(d\right), w\left(j\right) = i$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.pure` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

A pure word consists entirely of one letter; its length can be zero in this definition.

**Definition 1.8 (Projection onto pure words).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \operatorname{pureProjection}\left(n, d\right) = \operatorname{Matrix.diagonal}\left((w:\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(n\right)) \mapsto \operatorname{ite}\left(\operatorname{pure}\left(w\right), (1:\mathbb{C}), (0:\mathbb{C})\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.pureProjection` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

The diagonal is one exactly on the pure words, and zero on the mixed words.

**Definition 1.9 (The sharp residual matrix).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \operatorname{sharpGram}\left(n, d\right) = \operatorname{gram}\left(n, d\right) - ((\operatorname{mu}\left(n, d\right):\mathbb{C})) \cdot (\operatorname{pureProjection}\left(n, d\right))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.sharpGram` (`✓ std3`).

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

This is the word-indexed residual matrix G minus mu times the pure-word projection.

**Definition 1.10 (Pairing two half-words).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, \operatorname{gramWordEquiv}\left(n, d\right) = \operatorname{Equiv.trans}\left(\operatorname{Equiv.prodCongr}\left(\operatorname{Equiv.piCongrLeft'}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Fin.revPerm}\right), \operatorname{Equiv.refl}\left(\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(n\right)\right)\right), \operatorname{Fin.appendEquiv}\left(d, d\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.gramWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equiv.piCongrLeft' transports the first half through Fin.revPerm; Fin.appendEquiv then joins the two halves.

**Theorem 1.11 (Reversal preserves occupations).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), \forall i:\operatorname{Fin}\left(n\right), \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(\operatorname{Equiv.piCongrLeft'}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Fin.revPerm}\right)\left(w\right)\right)\right) = \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.count_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversal permutes positions without changing any letter multiplicity.

**Theorem 1.12 (The head contribution).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall i:\operatorname{Fin}\left(n\right), \forall j:\operatorname{Fin}\left(n\right), \forall w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), \operatorname{Multiset.count}\left(j, \operatorname{occupation}\left(\operatorname{Fin.cons}\left(i, w\right)\right)\right) = \operatorname{ite}\left(j = i, 1, 0\right) + \operatorname{Multiset.count}\left(j, \operatorname{occupation}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.count_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin.cons adds one occurrence of its head letter.

**Theorem 1.13 (A constant word count).**

$$\forall n:\mathbb{N}, \forall m:\mathbb{N}, \forall i:\operatorname{Fin}\left(n\right), \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(m\right), i\right)\right)\right) = m$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.count_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant word of length m has m occurrences of its letter.

**Theorem 1.14 (Concatenation adds counts).**

$$\forall n:\mathbb{N}, \forall a:\mathbb{N}, \forall b:\mathbb{N}, \forall u:\operatorname{Fin}\left(a\right) \to \operatorname{Fin}\left(n\right), \forall v:\operatorname{Fin}\left(b\right) \to \operatorname{Fin}\left(n\right), \forall i:\operatorname{Fin}\left(n\right), \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(\operatorname{Fin.append}\left(u, v\right)\right)\right) = \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(u\right)\right) + \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.count_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupation_append identity gives addition of letter counts.

**Theorem 1.15 (Evaluation of concatenation).**

$$\forall n:\mathbb{N}, \forall a:\mathbb{N}, \forall b:\mathbb{N}, \forall A:\operatorname{Type}, [\operatorname{Monoid}\left(A\right)] \forall X:\operatorname{Fin}\left(n\right) \to A, \forall u:\operatorname{Fin}\left(a\right) \to \operatorname{Fin}\left(n\right), \forall v:\operatorname{Fin}\left(b\right) \to \operatorname{Fin}\left(n\right), \operatorname{wordEval}\left(X, \operatorname{Fin.append}\left(u, v\right)\right) = \operatorname{wordEval}\left(X, u\right) \cdot \operatorname{wordEval}\left(X, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.word_eval_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered product of a concatenation is the product of the two ordered products.

**Theorem 1.16 (Reversal and adjoints).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall A:\operatorname{Type}, [\operatorname{Monoid}\left(A\right)] [\operatorname{StarMul}\left(A\right)] \forall X:\operatorname{Fin}\left(n\right) \to A, (\forall i:\operatorname{Fin}\left(n\right), \operatorname{IsSelfAdjoint}\left(X\left(i\right)\right)) \Rightarrow (\forall w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right), \operatorname{wordEval}\left(X, \operatorname{Equiv.piCongrLeft'}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Fin.revPerm}\right)\left(w\right)\right) = \operatorname{star}\left(\operatorname{wordEval}\left(X, w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.word_eval_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For self-adjoint letters, reversing the word gives the star of its evaluation.

**Definition 1.17 (The multidegree of a word).**

$$\forall n:\mathbb{N}, \forall m:\mathbb{N}, \forall w:\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right), \forall i:\operatorname{Fin}\left(n\right), \operatorname{val}\left(\operatorname{val}\left(\operatorname{wordDegree}\left(w\right)\right)\left(i\right)\right) = \operatorname{Multiset.count}\left(i, \operatorname{occupation}\left(w\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.wordDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value belongs to the subtype of a : Fin n -> Fin(m+1) with sum_i (a i : Nat) = m. Each displayed val is the actual subtype or Fin projection; these coordinates determine the constructor completely.

**Definition 1.18 (Shifted factorial moments).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall a:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \forall b:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \operatorname{factorialMoment}\left(g, a, b\right) = \prod_{i:\operatorname{Fin}\left(n\right)} ((\operatorname{Nat.factorial}\left((a\left(i\right):\mathbb{N}) + (b\left(i\right):\mathbb{N}) + g\left(i\right)\right):\mathbb{R}))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.factorialMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite kernel is the product of shifted factorials.

**Definition 1.19 (Binomial factorial features).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall a:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \forall k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \operatorname{factorialFeature}\left(g, a, k\right) = \prod_{i:\operatorname{Fin}\left(n\right)} ((\operatorname{Nat.factorial}\left((a\left(i\right):\mathbb{N}) + g\left(i\right)\right):\mathbb{R}) \cdot (\operatorname{Nat.choose}\left((a\left(i\right):\mathbb{N}), (k\left(i\right):\mathbb{N})\right):\mathbb{R}))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.factorialFeature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The feature is the product of factorials and natural binomial coefficients.

**Definition 1.20 (Positive Gram weights).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \operatorname{factorialWeight}\left(g, k\right) = \prod_{i:\operatorname{Fin}\left(n\right)} (\frac{(\operatorname{Nat.factorial}\left((k\left(i\right):\mathbb{N})\right):\mathbb{R})}{(\operatorname{Nat.factorial}\left(g\left(i\right) + (k\left(i\right):\mathbb{N})\right):\mathbb{R})})$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.factorialWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weights are products of positive real factorial ratios.

**Theorem 1.21 (Diagonal degree features).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall d:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall a:\{a:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right) \mid \sum_{i:\operatorname{Fin}\left(n\right)} ((a\left(i\right):\mathbb{N})) = d\}, \forall b:\{a:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right) \mid \sum_{i:\operatorname{Fin}\left(n\right)} ((a\left(i\right):\mathbb{N})) = d\}, (a \ne b) \Rightarrow (\operatorname{factorialFeature}\left(g, \operatorname{val}\left(b\right), \operatorname{val}\left(a\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.degree_feature_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct multidegrees of equal total degree have a coordinate exceeding the other; the corresponding binomial coefficient vanishes.

**Theorem 1.22 (Strictly positive diagonal features).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall a:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), 0 < \operatorname{factorialFeature}\left(g, a, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.factorial_feature_self_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every diagonal binomial coefficient is one and every factorial is positive.

**Theorem 1.23 (Strictly positive weights).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), 0 < \operatorname{factorialWeight}\left(g, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.factorial_weight_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every numerator and denominator factorial is positive.

**Theorem 1.24 (The finite factorial Gram identity).**

$$\forall n:\mathbb{N}, \forall B:\mathbb{N}, \forall g:\operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall a:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \forall b:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right), \operatorname{factorialMoment}\left(g, a, b\right) = \sum_{k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(B + 1\right)} (\operatorname{factorialWeight}\left(g, k\right) \cdot \operatorname{factorialFeature}\left(g, a, k\right) \cdot \operatorname{factorialFeature}\left(g, b, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.factorial_moment_gram` (`✓ std3`). ∎

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Vandermonde convolution gives the one-coordinate identity. Taking products gives this finite Gram factorization. No originality claim is made for the scalar identity.

**Definition 1.25 (The Hilbert-valued matrix form).**

$$\forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall I:\operatorname{Type}, [\operatorname{Fintype}\left(I\right)] \forall D:\operatorname{Matrix}\left(I, I, \mathbb{C}\right), \forall v:I \to H, \operatorname{matrixForm}\left(D, v\right) = \sum_{i:I} (\operatorname{inner}\left(\mathbb{C}, v\left(i\right), ((D) \cdot (v))\left(i\right)\right))$$

*Formalization.* `D5/S3/Analytic/Hunter/NCHunterPositivity.matrixForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The action D dot v is Mathlib Matrix.Module scalar multiplication, not entrywise scalar multiplication. The form uses the complex inner product, conjugate-linear in its first entry.

**Theorem 1.26 (Zero form implies zero rows).**

$$\forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall I:\operatorname{Type}, [\operatorname{Fintype}\left(I\right)] \forall D:\operatorname{Matrix}\left(I, I, \mathbb{C}\right), \forall v:I \to H, (\operatorname{Matrix.PosSemidef}\left(D\right)) \Rightarrow ((\operatorname{matrixForm}\left(D, v\right) = 0) \Rightarrow (\forall i:I, ((D) \cdot (v))\left(i\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.positive_form_zero_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive semidefinite matrix factors as B-star times B. The form is a sum of squared Hilbert norms, forcing every row to vanish.

**Theorem 1.27 (Strict positivity gives zero coefficients).**

$$\forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] \forall I:\operatorname{Type}, [\operatorname{Fintype}\left(I\right)] \forall D:\operatorname{Matrix}\left(I, I, \mathbb{C}\right), \forall v:I \to H, (\operatorname{Matrix.PosDef}\left(D\right)) \Rightarrow ((\operatorname{matrixForm}\left(D, v\right) = 0) \Rightarrow (\forall i:I, v\left(i\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.positive_definite_form_zero_vectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the rows vanish, invertibility of the positive definite matrix forces every coefficient vector to vanish.

**Theorem 1.28 (Splitting the leading letter).**

$$\forall n:\mathbb{N}, \forall k:\mathbb{N}, \forall A:\operatorname{Type}, [\operatorname{AddCommMonoid}\left(A\right)] \forall f:\left(\operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(n\right)\right) \to A, \sum_{w:\operatorname{Fin}\left(k + 1\right) \to \operatorname{Fin}\left(n\right)} (f\left(w\right)) = \sum_{i:\operatorname{Fin}\left(n\right)} (\sum_{w:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right)} (f\left(\operatorname{Fin.cons}\left(i, w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.sum_word_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin.consEquiv partitions all words of positive length by their leading letter.

**Theorem 1.29 (The operator form equals the Gram form).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, (0 < d) \Rightarrow (\forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] [\operatorname{CompleteSpace}\left(H\right)] \forall X:\operatorname{Fin}\left(n\right) \to \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right), (\forall i:\operatorname{Fin}\left(n\right), \operatorname{IsSelfAdjoint}\left(X\left(i\right)\right)) \Rightarrow (\forall h:H, \operatorname{inner}\left(\mathbb{C}, h, \operatorname{residual}\left(n, d, X\right)\left(h\right)\right) = \operatorname{matrixForm}\left(\operatorname{sharpGram}\left(n, d\right), (w:\operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(n\right)) \mapsto \operatorname{wordEval}\left(X, w\right)\left(h\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.residual_inner_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reversed-word pairing converts the operator form into the word Gram form; the pure diagonal extracts the even powers.

**Theorem 1.30 (Positivity at the sharp constant).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, (2 \le n) \Rightarrow ((0 < d) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(\operatorname{sharpGram}\left(n, d\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.sharp_gram_posSemidef` (`✓ std3`). ∎

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Garcia--Volcic, Proposition 3.3, pages 8--9. Explicit inverse columns satisfy G R = E. The positive decomposition uses P = I - mu R E-transpose and the nonnegative pure block.

**Theorem 1.31 (The sharp operator inequality).**

$$\forall n:\mathbb{N}, \forall d:\mathbb{N}, (0 < n) \Rightarrow ((0 < d) \Rightarrow (\forall H:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] [\operatorname{CompleteSpace}\left(H\right)] \forall X:\operatorname{Fin}\left(n\right) \to \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right), (\forall i:\operatorname{Fin}\left(n\right), \operatorname{IsSelfAdjoint}\left(X\left(i\right)\right)) \Rightarrow (((\operatorname{mu}\left(n, d\right):\mathbb{C})) \cdot (\sum_{i:\operatorname{Fin}\left(n\right)} (X\left(i\right)^{2 \cdot d})) \le \operatorname{nchs}\left(n, 2 \cdot d, X\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hunter/NCHunterPositivity.sharp_positivity` (`✓ std3`). ∎

*Citation.* S. R. Garcia and J. Volčič (2025). *A noncommutative generalization of Hunter's positivity theorem*. DOI: [10.1090/proc/17480](https://doi.org/10.1090/proc/17480). URL: <https://arxiv.org/abs/2503.12376v2>.

*Commentary.*

Theorem 1.1(ii), pages 2–3: “Let $n,d\in\mathbb{N}$. For all $k\in\mathbb{N}$ and all hermitian operators $X_{1}$…, $X_{n}$ on a Hilbert space, $H_{2d}$($X_{1}$,…, $X_{n}$) ⪰ $\mu_{n,d}$ ($X_{1}^{2d}$ + ⋯ + $X_{n}^{2d}$),” in which the source defines the Löwner partial order and the three cases of the constant.

The Lean carrier is a complete complex inner-product space and bounded complex-linear operators. The zero-based alphabet Fin n reindexes the source letters. The n = 1 case is equality.

## References

- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.coefficient`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.count_append`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.count_cons`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.count_constant`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.count_reverse`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.degree_feature_diagonal`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.factorialFeature`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.factorialMoment`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.factorialWeight`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.factorial_feature_self_pos`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.factorial_moment_gram`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.factorial_weight_pos`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.gram`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.gramWordEquiv`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.matrixForm`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.mu`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.nchs`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.positive_definite_form_zero_vectors`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.positive_form_zero_rows`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.pure`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.pureProjection`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.residual`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.residual_inner_gram`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.sharpGram`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.sharp_gram_posSemidef`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.sharp_positivity`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.sum_word_succ`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.wordDegree`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.wordEval`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.word_eval_append`
- Truth anchor: `D5/S3/Analytic/Hunter/NCHunterPositivity.word_eval_reverse`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../../Quantum/Entanglement/OccupancyWordSectors.md)
