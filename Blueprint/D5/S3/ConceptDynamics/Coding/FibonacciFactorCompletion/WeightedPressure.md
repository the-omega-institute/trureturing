# Weighted pressure of the actual bilateral language

## Abstract

The actual occurring-word pressure has the original sparse weighted factor rate as its unique zero.

For the nonempty binary bilateral subshift X of source lemma 62.16, every word is indexed once regardless of how many configurations or positions realize it. The letters u and c have weights six and twenty. The formulas also hold for arbitrary nonempty sets of bilateral configurations; closedness and shift invariance of the source subshift are retained without a graph, a run cap, or a positive-entropy requirement.

**Definition 1.1 (OccurringWord).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{OccurringWord}\left(X\right) = \operatorname{subtype}\left((w : \operatorname{List}\left(CuLetter\right) \mapsto \exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, X\right) \land \operatorname{Occurs}\left(omega, w\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.OccurringWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An element consists of the finite letter list and the proposition that it occurs in some configuration of X. Proofs and occurrence positions do not supply extra indices.

**Definition 1.2 (LengthDictionary).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall k \in Nat,\; \operatorname{LengthDictionary}\left(X, k\right) = \operatorname{subtype}\left((w : \operatorname{List}\left(CuLetter\right) \mapsto \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, X\right) \land \operatorname{Occurs}\left(omega, w\right)\right) \land \operatorname{length}\left(w\right) = k)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.LengthDictionary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dictionary contains exactly the actual occurring words of length k, including the empty word when k is zero.

**Theorem 1.3 (lengthDictionary finite).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall k \in Nat,\; \operatorname{Finite}\left(\operatorname{LengthDictionary}\left(X, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.lengthDictionary_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Indexing a length-k list by Fin k injects the dictionary into the finite set of binary k-tuples.

**Theorem 1.4 (length dictionary nonempty).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall k \in Nat,\; \operatorname{Nonempty}\left(\operatorname{LengthDictionary}\left(X, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.length_dictionary_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict any configuration of X to positions zero through k minus one. This gives an occurring word at every length, including zero.

**Definition 1.5 (wordTerm).**

$$\forall theta \in Real, w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{wordTerm}\left(theta, w\right) = \operatorname{power}\left(\operatorname{power}\left(2, \operatorname{negate}\left(theta\right)\right), \operatorname{wordWeight}\left(w\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.wordTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural-power monomial is exactly two to minus theta times the original total word weight.

**Definition 1.6 (partitionSum).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \forall k \in Nat,\; \operatorname{partitionSum}\left(X, k, theta\right) = \operatorname{sum}\left((w : \operatorname{LengthDictionary}\left(X, k\right) \mapsto \operatorname{wordTerm}\left(theta, \operatorname{val}\left(w\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partitionSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real partition sum is finite and counts each actual word once.

**Definition 1.7 (logPartition).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \forall k \in Nat,\; \operatorname{logPartition}\left(X, theta, k\right) = \operatorname{logb}\left(2, \operatorname{partitionSum}\left(X, k, theta\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.logPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The logarithm is in base two.

**Definition 1.8 (pressure).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \operatorname{pressure}\left(X, theta\right) = \operatorname{sInf}\left(\operatorname{image}\left((k : Nat \mapsto \operatorname{divide}\left(\operatorname{logPartition}\left(X, theta, k\right), \operatorname{toReal}\left(k\right)\right)), \operatorname{Ici}\left(1\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pressure is the infimum of all positive-length logarithmic quotients. Length zero is excluded from this infimum.

**Theorem 1.9 (partition positive).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \forall k \in Nat,\; \operatorname{lt}\left(0, \operatorname{partitionSum}\left(X, k, theta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every monomial is strictly positive and every length dictionary is nonempty.

**Definition 1.10 (splitWord).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall k \in Nat, j \in Nat,\; \operatorname{hasType}\left(\operatorname{splitWord}\left(X, k, j\right), \operatorname{LengthDictionary}\left(X, \operatorname{add}\left(k, j\right)\right) \to \operatorname{Product}\left(\operatorname{LengthDictionary}\left(X, k\right), \operatorname{LengthDictionary}\left(X, j\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.splitWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the first k letters and drop those k letters. Both pieces occur in the same realizing configuration, at the original position and at its translate by k.

**Theorem 1.11 (split word injective).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall k \in Nat, j \in Nat,\; \operatorname{Injective}\left(\operatorname{splitWord}\left(X, k, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.split_word_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending the two pieces recovers the original word. No pair is counted more than once.

**Theorem 1.12 (partition submultiplicative).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \forall k \in Nat, j \in Nat,\; \operatorname{le}\left(\operatorname{partitionSum}\left(X, \operatorname{add}\left(k, j\right), theta\right), \operatorname{multiply}\left(\operatorname{partitionSum}\left(X, k, theta\right), \operatorname{partitionSum}\left(X, j, theta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_submultiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weight is additive under append. The split injection embeds the summands into the product dictionary, whose remaining monomials are nonnegative.

**Theorem 1.13 (log partition subadditive).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \operatorname{Subadditive}\left((k : Nat \mapsto \operatorname{logPartition}\left(X, theta, k\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.log_partition_subadditive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive partition sums allow the submultiplicative inequality to pass to their actual logarithms.

**Theorem 1.14 (partition lower bound).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \forall k \in Nat,\; \operatorname{le}\left(\operatorname{power}\left(2, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{negate}\left(20\right), \operatorname{abs}\left(theta\right)\right), \operatorname{toReal}\left(k\right)\right)\right), \operatorname{partitionSum}\left(X, k, theta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One occurring word, with weight at most twenty times its length, gives this lower bound uniformly in X and k for every real theta.

**Theorem 1.15 (log quotient lower bound).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \forall k \in Nat,\; \operatorname{le}\left(\operatorname{multiply}\left(\operatorname{negate}\left(20\right), \operatorname{abs}\left(theta\right)\right), \operatorname{divide}\left(\operatorname{logPartition}\left(X, theta, k\right), \operatorname{toReal}\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.log_quotient_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic quotient is bounded below by minus twenty times the absolute value of theta. At k equal to zero the real quotient is zero, so the same bound remains valid.

**Theorem 1.16 (pressure tendsto).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \operatorname{Tendsto}\left((k : Nat \mapsto \operatorname{divide}\left(\operatorname{logPartition}\left(X, theta, k\right), \operatorname{toReal}\left(k\right)\right)), atTop, \operatorname{nhds}\left(\operatorname{pressure}\left(X, theta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fekete's lemma applies to the derived subadditive logarithms and the proved uniform quotient lower bound. Its limit is the exact infimum over every k at least one.

**Theorem 1.17 (partition shift bounds).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \forall k \in Nat, a \in Real,\; \operatorname{le}\left(0, a\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{multiply}\left(\operatorname{power}\left(2, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{negate}\left(20\right), a\right), \operatorname{toReal}\left(k\right)\right)\right), \operatorname{partitionSum}\left(X, k, theta\right)\right), \operatorname{partitionSum}\left(X, k, \operatorname{add}\left(theta, a\right)\right)\right) \land \operatorname{le}\left(\operatorname{partitionSum}\left(X, k, \operatorname{add}\left(theta, a\right)\right), \operatorname{multiply}\left(\operatorname{power}\left(2, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{negate}\left(6\right), a\right), \operatorname{toReal}\left(k\right)\right)\right), \operatorname{partitionSum}\left(X, k, theta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_shift_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative shift a, each exponent uses the same word weight between six k and twenty k. Summing preserves both bounds.

**Theorem 1.18 (pressure shift bounds).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \forall a \in Real,\; \operatorname{le}\left(0, a\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{subtract}\left(\operatorname{pressure}\left(X, theta\right), \operatorname{multiply}\left(20, a\right)\right), \operatorname{pressure}\left(X, \operatorname{add}\left(theta, a\right)\right)\right) \land \operatorname{le}\left(\operatorname{pressure}\left(X, \operatorname{add}\left(theta, a\right)\right), \operatorname{subtract}\left(\operatorname{pressure}\left(X, theta\right), \operatorname{multiply}\left(6, a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_shift_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide the logarithmic partition bounds by positive k and pass to the proved limits. The source's slopes are minus twenty and minus six, with the zero-shift case included.

**Theorem 1.19 (pressure lipschitz).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{LipschitzWith}\left(20, (theta : Real \mapsto \operatorname{pressure}\left(X, theta\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two slope bounds give a global Lipschitz constant of twenty, hence continuity on the whole real line.

**Theorem 1.20 (pressure strictAnti).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{StrictAnti}\left((theta : Real \mapsto \operatorname{pressure}\left(X, theta\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper slope bound decreases pressure strictly whenever the exponent increases.

**Theorem 1.21 (pressure zero nonneg).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{le}\left(0, \operatorname{pressure}\left(X, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_zero_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At theta zero every word contributes one. Nonemptiness makes every logarithmic quotient nonnegative; zero entropy is allowed.

**Theorem 1.22 (pressure unique zero).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \operatorname{existsUnique}\left((eta : Real \mapsto \operatorname{le}\left(0, eta\right) \land \operatorname{pressure}\left(X, eta\right) = 0)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_unique_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity, P at zero nonnegative, and the literal upper slope give a nonnegative zero by the intermediate value theorem. Strict decrease makes it unique.

**Theorem 1.23 (whole series regrouping).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \operatorname{tsum}\left((w : \operatorname{OccurringWord}\left(X\right) \mapsto \operatorname{ofReal}\left(\operatorname{wordTerm}\left(theta, \operatorname{val}\left(w\right)\right)\right))\right) = \operatorname{tsum}\left((k : Nat \mapsto \operatorname{ofReal}\left(\operatorname{partitionSum}\left(X, k, theta\right)\right))\right) \land \operatorname{tsum}\left((w : \operatorname{OccurringWord}\left(X\right) \mapsto \operatorname{ofReal}\left(\operatorname{wordTerm}\left(theta, \operatorname{val}\left(w\right)\right)\right))\right) = \operatorname{tsum}\left((T : Nat \mapsto \operatorname{ofReal}\left(\operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{factorCount}\left(X, T\right)\right), \operatorname{power}\left(\operatorname{power}\left(2, \operatorname{negate}\left(theta\right)\right), T\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.whole_series_regrouping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition the exact occurring-word index by length and then by original weight. The length fiber is the finite length dictionary; the weight fiber is the original finite FactorDictionary and contributes factorCount times the constant monomial. Both ENNReal equalities include infinity.

**Theorem 1.24 (whole series finiteness).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \forall theta \in Real,\; \left(\operatorname{Summable}\left((k : Nat \mapsto \operatorname{partitionSum}\left(X, k, theta\right))\right) \Leftrightarrow \operatorname{lt}\left(\operatorname{tsum}\left((w : \operatorname{OccurringWord}\left(X\right) \mapsto \operatorname{ofReal}\left(\operatorname{wordTerm}\left(theta, \operatorname{val}\left(w\right)\right)\right))\right), infinity\right)\right) \land \left(\operatorname{Summable}\left((T : Nat \mapsto \operatorname{multiply}\left(\operatorname{toReal}\left(\operatorname{factorCount}\left(X, T\right)\right), \operatorname{power}\left(\operatorname{power}\left(2, \operatorname{negate}\left(theta\right)\right), T\right)\right))\right) \Leftrightarrow \operatorname{lt}\left(\operatorname{tsum}\left((w : \operatorname{OccurringWord}\left(X\right) \mapsto \operatorname{ofReal}\left(\operatorname{wordTerm}\left(theta, \operatorname{val}\left(w\right)\right)\right))\right), infinity\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.whole_series_finiteness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The meaningful ENNReal condition is that the whole sum is less than infinity. It is equivalent to real summability for both regroupings. Bare ENNReal Summable imposes no finiteness condition.

**Theorem 1.25 (whole series nonpositive).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \operatorname{le}\left(theta, 0\right) \Rightarrow \operatorname{tsum}\left((w : \operatorname{OccurringWord}\left(X\right) \mapsto \operatorname{ofReal}\left(\operatorname{wordTerm}\left(theta, \operatorname{val}\left(w\right)\right)\right))\right) = infinity\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.whole_series_nonpositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual words of every length give an injection of the natural numbers into the occurring-word index. At nonpositive theta all their monomials are at least one, so the whole sum is infinite.

**Theorem 1.26 (negative pressure summable).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \operatorname{lt}\left(\operatorname{pressure}\left(X, theta\right), 0\right) \Rightarrow \operatorname{Summable}\left((k : Nat \mapsto \operatorname{partitionSum}\left(X, k, theta\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.negative_pressure_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A negative limit of the logarithmic quotients gives an eventual geometric majorant of ratio less than one.

**Theorem 1.27 (pressure zero iff rate).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{Nonempty}\left(X\right) \Rightarrow \left(\forall theta \in Real,\; \operatorname{pressure}\left(X, theta\right) = 0 \Leftrightarrow theta = \operatorname{weightedFactorRate}\left(X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_zero_iff_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original factor_rate_convergence criterion applies at positive exponents through the exact whole-series correspondence. Nonpositive exponents diverge. If the zero and the sparse max-one weightedFactorRate differed, an exponent strictly between them would contradict either geometric convergence or pressure strictness. Unsupported weights stay in the original count sequence. No convergence claim at the zero is used.

These formulas establish source lemma 62.16. Nested compact-language stabilization and pressure limits, same-reset actual and bilateral codebooks, actual-list count bridges, and all-even source-length asymptotics require their respective additional constructions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.LengthDictionary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.OccurringWord`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.lengthDictionary_finite`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.length_dictionary_nonempty`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.logPartition`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.log_partition_subadditive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.log_quotient_lower_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.negative_pressure_summable`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partitionSum`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_lower_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_positive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_shift_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.partition_submultiplicative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_lipschitz`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_shift_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_strictAnti`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_tendsto`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_unique_zero`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_zero_iff_rate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.pressure_zero_nonneg`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.splitWord`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.split_word_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.whole_series_finiteness`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.whole_series_nonpositive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.whole_series_regrouping`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.wordTerm`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot](InteriorRoot.md)
