# Minimal winning advantage for fair dice

## Abstract

Sorted dice and exact unconditional probabilities describe minimal-advantage simple cycles.

**Definition 1.1 (Valid sorted dice).**

$$\forall n \in \mathit{Nat}, d \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{IsDie}\left(n, d\right) \Leftrightarrow \left(\left(\operatorname{length}\left(d\right) = n \land \left(\forall i \in \operatorname{Fin}\left(\operatorname{length}\left(d\right)\right), j \in \operatorname{Fin}\left(\operatorname{length}\left(d\right)\right),\; i < j \Rightarrow \operatorname{at}\left(d, i\right) \le \operatorname{at}\left(d, j\right)\right)\right) \land \left(\forall x \in \mathit{Nat},\; x \in d \Rightarrow \left(1 \le x \land x \le n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.IsDie` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n and list d of natural labels, IsDie(n,d) means that d has length n, is pairwise nondecreasing, and each face x occurring in d satisfies 1 ≤ x ≤ n. Repeated labels and the standard tuple are permitted.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.2 (Strict winning ordered outcomes).**

$$\forall d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{winCount}\left(d, e\right) = \operatorname{sum}\left(\left(\operatorname{sum}\left(\left(\operatorname{ite}\left(\operatorname{at}\left(e, v\right) < \operatorname{at}\left(d, u\right), 1, 0\right)\right)_{v \in \operatorname{Fin}\left(\operatorname{length}\left(e\right)\right)}\right)\right)_{u \in \operatorname{Fin}\left(\operatorname{length}\left(d\right)\right)}\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.winCount` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For any two lists d and e of natural labels, winCount(d,e) is the sum over occurrences x in d and y in e of the indicator of y < x. Repeated labels retain their multiplicities and ties contribute zero.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.3 (Strict wins on the independent index product).**

$$\forall d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{indexWinCount}\left(d, e\right) = \operatorname{sum}\left(\left(\operatorname{sum}\left(\left(\operatorname{ite}\left(\operatorname{at}\left(e, v\right) < \operatorname{at}\left(d, u\right), 1, 0\right)\right)_{v \in \operatorname{Fin}\left(\operatorname{length}\left(e\right)\right)}\right)\right)_{u \in \operatorname{Fin}\left(\operatorname{length}\left(d\right)\right)}\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.indexWinCount` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For all lists d,e, indexWinCount(d,e) is the sum over i in Fin(length(d)) and j in Fin(length(e)) of the indicator of e[j] < d[i]. Both indices vary over their whole finite domains independently.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.4 (Unconditional uniform strict-win probability).**

$$\forall d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{winProbability}\left(d, e\right) = \frac{\operatorname{NatToRat}\left(\operatorname{indexWinCount}\left(d, e\right)\right)}{\operatorname{NatToRat}\left(\operatorname{length}\left(d\right) \cdot \operatorname{length}\left(e\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.winProbability` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For all lists d,e, winProbability(d,e) is the rational indexWinCount(d,e) divided by length(d) times length(e). For nonempty dice this gives every ordered independent pair of face indices the same probability and leaves ties in the denominator.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.5 (The least integer above half the outcome count).**

$$\forall n \in \mathit{Nat},\; \operatorname{threshold}\left(n\right) = \left\lfloor\frac{n \cdot n}{2}\right\rfloor + 1$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n, threshold(n) = floor(n²/2) + 1. This is an integer score; its attainability by valid dice is a separate assertion.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.6 (The true attained minimum).**

$$\forall n \in \mathit{Nat}, p \in \mathit{Rat},\; \operatorname{IsMinimum}\left(n, p\right) \Leftrightarrow \left(\left(\left(\exists d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\operatorname{IsDie}\left(n, d\right) \land \operatorname{IsDie}\left(n, e\right)\right) \land \operatorname{winProbability}\left(d, e\right) = p\right) \land \frac{1}{2} < p\right) \land \left(\forall d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\left(\operatorname{IsDie}\left(n, d\right) \land \operatorname{IsDie}\left(n, e\right)\right) \land \frac{1}{2} < \operatorname{winProbability}\left(d, e\right)\right) \Rightarrow p \le \operatorname{winProbability}\left(d, e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.IsMinimum` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n and rational p, IsMinimum(n,p) requires valid n-face dice d,e with winProbability(d,e)=p, requires p>1/2, and requires p≤winProbability(a,b) for every valid ordered pair a,b with winProbability(a,b)>1/2.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.7 (Minimum-advantage directed edges).**

$$\forall n \in \mathit{Nat}, d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{Edge}\left(n, d, e\right) \Leftrightarrow \left(\left(\operatorname{IsDie}\left(n, d\right) \land \operatorname{IsDie}\left(n, e\right)\right) \land \operatorname{IsMinimum}\left(n, \operatorname{winProbability}\left(d, e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.Edge` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For natural n and lists d,e, Edge(n,d,e) requires that both are valid n-face dice and that their actual unconditional strict-win probability is an attained minimum among all probabilities above one half.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.8 (Simple cycles with their closing edge).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat},\; \operatorname{HasCycle}\left(n, k\right) \Leftrightarrow \left(\exists c \in \operatorname{List}\left(\operatorname{List}\left(\mathit{Nat}\right)\right),\; \left(\left(\operatorname{length}\left(c\right) = k \land \operatorname{Nodup}\left(c\right)\right) \land c \ne \operatorname{nil}\left(\right)\right) \land \operatorname{IsChain}\left(\operatorname{Edge}\left(n\right), \operatorname{append}\left(c, \operatorname{singleton}\left(\operatorname{head}\left(c\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.HasCycle` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For natural n,k, HasCycle(n,k) means there is a nonempty list c of exactly k pairwise distinct dice such that c followed by its first entry is a chain for Edge(n). The last-to-first edge is included and no vertex can be reused.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.9 (An exact global maximum).**

$$\forall n \in \mathit{Nat},\; \operatorname{S}\left(n\right) \Leftrightarrow \left(\operatorname{HasCycle}\left(n, n\right) \land \left(\forall k \in \mathit{Nat},\; n < k \Rightarrow \left(\neg \operatorname{HasCycle}\left(n, k\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.S` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n, S(n) means HasCycle(n,n) and, for every natural k>n, the negation of HasCycle(n,k). Thus the bound concerns all simple cycles in the entire graph.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.10 (The complete conjecture).**

$$\operatorname{ConjectureOne}\left(\right) \Leftrightarrow \left(\operatorname{S}\left(6\right) \land \left(\forall n \in \mathit{Nat},\; 7 \le n \Rightarrow \left(\neg \operatorname{S}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.ConjectureOne` (`✓ std3`).

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

ConjectureOne is the proposition S(6) and, for every natural n≥7, not S(n). It imposes no condition at three, four or five, and it does not assume the existence of longer cycles.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.11 (The occurrence-to-index counting bridge).**

$$\forall d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{winCount}\left(d, e\right) = \operatorname{indexWinCount}\left(d, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.winCount_eq_indexWinCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For all lists d and e of natural labels, winCount(d,e)=indexWinCount(d,e). Each occurrence in a list is recovered from its face index, so multiplicities are preserved in the equality.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.12 (Attainment for every n at least three).**

$$\forall n \in \mathit{Nat},\; 3 \le n \Rightarrow \left(\exists d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\operatorname{IsDie}\left(n, d\right) \land \operatorname{IsDie}\left(n, e\right)\right) \land \operatorname{winCount}\left(d, e\right) = \operatorname{threshold}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.threshold_attained` (`✓ std3`). ∎

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n≥3 there exist valid sorted n-face dice d,e whose strict-win count is threshold(n). For n=2k the dice are 1 repeated k−1 times, then 2, then 3 repeated k times, against 1 followed by 2 repeated 2k−1 times. For n=2k+1 they are 1 repeated k times, then 2, then 3 repeated k times, against 1 repeated k+1 times followed by 2 repeated k times.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.13 (The exact integer-grid condition).**

$$\forall n \in \mathit{Nat}, d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\left(0 < n \land \operatorname{IsDie}\left(n, d\right)\right) \land \operatorname{IsDie}\left(n, e\right)\right) \Rightarrow \left(\frac{1}{2} < \operatorname{winProbability}\left(d, e\right) \Leftrightarrow \operatorname{threshold}\left(n\right) \le \operatorname{winCount}\left(d, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.above_half_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n>0 and all valid sorted n-face dice d,e, winProbability(d,e)>1/2 if and only if threshold(n)≤winCount(d,e).

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.14 (The actual attained minimum).**

$$\forall n \in \mathit{Nat},\; 3 \le n \Rightarrow \operatorname{IsMinimum}\left(n, \frac{\operatorname{NatToRat}\left(\operatorname{threshold}\left(n\right)\right)}{\operatorname{NatToRat}\left(n \cdot n\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.minimum_probability` (`✓ std3`). ∎

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n≥3, IsMinimum(n,threshold(n)/n²). The explicit attaining pair supplies existence, and the integer-grid condition bounds every other actual probability above one half.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.15 (Edges are exactly threshold scores).**

$$\forall n \in \mathit{Nat}, d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\left(3 \le n \land \operatorname{IsDie}\left(n, d\right)\right) \land \operatorname{IsDie}\left(n, e\right)\right) \Rightarrow \left(\operatorname{Edge}\left(n, d, e\right) \Leftrightarrow \operatorname{winCount}\left(d, e\right) = \operatorname{threshold}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.edge_iff` (`✓ std3`). ∎

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural n≥3 and all valid n-face dice d,e, Edge(n,d,e) if and only if winCount(d,e)=threshold(n). This equivalence identifies the graph from the actual minimum among all ordered dice pairs.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Definition 1.16 (Nested interval padding).**

$$\forall b \in \mathit{Nat}, t \in \mathit{Nat}, j \in \mathit{Nat}, c \in \mathit{Bool}, d \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{padded}\left(b, t, j, c, d\right) = \operatorname{append}\left(\operatorname{replicate}\left(j, 1 + 2 \cdot \operatorname{toNat}\left(c\right)\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{NatSub}\left(t, j\right), 2 + 2 \cdot \operatorname{toNat}\left(c\right)\right), \operatorname{append}\left(\operatorname{shift}\left(d, 4\right), \operatorname{replicate}\left(t, \operatorname{NatSub}\left(b + 6, \operatorname{toNat}\left(c\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For natural b,t,j, a Boolean c and a seed list d, padded(b,t,j,c,d) concatenates j copies of 1+2c, t−j copies of 2+2c, the seed labels increased by four, and t copies of b+6−c, with c read as zero or one.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.17 (Exact score in both directions).**

$$\forall b \in \mathit{Nat}, t \in \mathit{Nat}, j \in \mathit{Nat}, k \in \mathit{Nat}, c \in \mathit{Bool}, d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\left(\left(j \le t \land k \le t\right) \land \left(\forall x \in \mathit{Nat},\; x \in d \Rightarrow \left(1 \le x \land x \le b\right)\right)\right) \land \left(\forall x \in \mathit{Nat},\; x \in e \Rightarrow \left(1 \le x \land x \le b\right)\right)\right) \Rightarrow \operatorname{winCount}\left(\operatorname{padded}\left(b, t, j, c, d\right), \operatorname{padded}\left(b, t, k, \operatorname{BoolNot}\left(c\right), e\right)\right) = \operatorname{winCount}\left(d, e\right) + t \cdot \operatorname{length}\left(d\right) + t \cdot \operatorname{length}\left(e\right) + 2 \cdot t \cdot t$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded_winCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For all naturals b,t,j,k with j≤t and k≤t, Boolean c, and seed lists d,e whose labels lie between one and b, the score from padded(b,t,j,c,d) to padded(b,t,k,not c,e) equals winCount(d,e)+t length(d)+t length(e)+2t². The two clone indices can be chosen independently.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.18 (The threshold under even padding).**

$$\forall r \in \mathit{Nat}, t \in \mathit{Nat},\; \operatorname{threshold}\left(r + 2 \cdot t\right) = \operatorname{threshold}\left(r\right) + 2 \cdot t \cdot r + 2 \cdot t \cdot t$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.threshold_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural r,t, threshold(r+2t)=threshold(r)+2tr+2t², with no restriction on the parity of r.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.19 (Sortedness and label bounds of padding).**

$$\forall r \in \mathit{Nat}, b \in \mathit{Nat}, t \in \mathit{Nat}, j \in \mathit{Nat}, c \in \mathit{Bool}, d \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\left(\left(\left(j \le t \land \operatorname{length}\left(d\right) = r\right) \land \left(\forall i \in \operatorname{Fin}\left(\operatorname{length}\left(d\right)\right), j \in \operatorname{Fin}\left(\operatorname{length}\left(d\right)\right),\; i < j \Rightarrow \operatorname{at}\left(d, i\right) \le \operatorname{at}\left(d, j\right)\right)\right) \land \left(\forall x \in \mathit{Nat},\; x \in d \Rightarrow \left(1 \le x \land x \le b\right)\right)\right) \land b + 6 \le r + 2 \cdot t\right) \Rightarrow \operatorname{IsDie}\left(r + 2 \cdot t, \operatorname{padded}\left(b, t, j, c, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded_isDie` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For all naturals r,b,t,j, Boolean c and list d, suppose j≤t, d has length r and is nondecreasing, all its labels lie in [1,b], and b+6≤r+2t. Then padded(b,t,j,c,d) is a valid sorted (r+2t)-face die.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

**Theorem 1.20 (Recovering seed and clone).**

$$\forall b \in \mathit{Nat}, t \in \mathit{Nat}, j \in \mathit{Nat}, k \in \mathit{Nat}, c \in \mathit{Bool}, cprime \in \mathit{Bool}, d \in \operatorname{List}\left(\mathit{Nat}\right), e \in \operatorname{List}\left(\mathit{Nat}\right),\; \left(\left(\left(\forall x \in \mathit{Nat},\; x \in d \Rightarrow \left(1 \le x \land x \le b\right)\right) \land \left(\forall x \in \mathit{Nat},\; x \in e \Rightarrow \left(1 \le x \land x \le b\right)\right)\right) \land \operatorname{padded}\left(b, t, j, c, d\right) = \operatorname{padded}\left(b, t, k, \mathit{cprime}, e\right)\right) \Rightarrow \left(d = e \land \left(c = \mathit{cprime} \Rightarrow j = k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded_eq_imp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For all naturals b,t,j,k, Booleans c,c′ and seed lists d,e with labels in [1,b], equality padded(b,t,j,c,d)=padded(b,t,k,c′,e) implies d=e and implies j=k whenever c=c′. Restricting to central labels recovers the seed and the first low-label multiplicity recovers the clone.

In the formulas, at selects a zero-based face or cycle position, sum sums every element of the displayed finite sequence, NatToRat is the natural-to-rational cast, NatSub is truncated natural subtraction, shift adds its displayed constant to each face, and head denotes head!; HasCycle separately requires a nonempty cycle. Boolean toNat sends false to zero and true to one. Rational division is total, with x divided by zero equal to zero; all graph applications use at least three faces. All finite face-index domains retain repeated-face multiplicities.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.ConjectureOne`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.Edge`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.HasCycle`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.IsDie`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.IsMinimum`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.S`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.above_half_iff`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.edge_iff`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.indexWinCount`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.minimum_probability`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded_eq_imp`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded_isDie`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.padded_winCount`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.threshold`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.threshold_attained`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.threshold_padding`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.winCount`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.winCount_eq_indexWinCount`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.winProbability`
