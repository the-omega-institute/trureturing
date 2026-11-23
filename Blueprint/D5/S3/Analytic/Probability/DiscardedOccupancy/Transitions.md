# Transitions of occupancy with discarded throws

## Abstract

A lower bound on early conditional variances gives a linear lower bound for the terminal variance.

**Theorem 1.1 (Variance from the early throws).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), 0<n \implies 0 \leq p \implies p \leq 1 \implies \lfloor \frac{n}{2} \rfloor \cdot \frac{p \cdot (1 - p)^{3}}{2} \leq \operatorname{variance}\left(n, p, n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here n is the number of ordinary bins and p is the total probability of assigning a throw to an ordinary bin. The trial following x occupied bins increases the count with probability p times one minus x divided by n. The exact weighted variance recursion yields the displayed bound from the first floor of n divided by two increments.

**Definition 1.2 (History).**

$$\forall (n: \mathbb{N}), \forall (j: \mathbb{N}), (\mathit{History} n j : \mathit{Type}) = \mathit{Fin} j \to \mathit{Option} (\mathit{Fin} n)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.History` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.3 (A).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), (a n p : \mathbb{R}) = 1 - p / \mathit{val} n$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.4 (A bounds).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), 0 \leq a n p \land a n p \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.a_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.5 (Average).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (f: \mathit{DiscardedOccupancy}.\mathit{History} n j \to E), (\mathit{average} E n p j f : E) = \sum \omega : \mathit{DiscardedOccupancy}.\mathit{History} n j, \mathit{wordMass} n p \omega \cdot f \omega$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.average` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.6 (Count).**

$$\forall (n: \mathbb{N}), \forall (j: \mathbb{N}), \forall (\omega: \mathit{DiscardedOccupancy}.\mathit{History} n j), (\mathit{count} n j \omega : \mathbb{N}) = (\mathit{occupied} n j \omega).\mathit{card}$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.7 (Expect).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (f: \mathbb{N} \to E), (\mathit{expect} E n p j f : E) = \mathit{average} n p j \mathit{fun} (\omega : \mathit{DiscardedOccupancy}.\mathit{History} n j) => f (\mathit{count} n j \omega)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.8 (Expect add).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (f: \mathbb{N} \to E), \forall (g: \mathbb{N} \to E), (\mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => f x + g x) = \mathit{expect} n p j f + \mathit{expect} n p j g$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.9 (Expect congr).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (j: \mathbb{N}), \forall (p: \mathbb{R}), \forall (f: \mathbb{N} \to E), \forall (g: \mathbb{N} \to E), \forall (h: \forall x \leq j, x \leq n \to f x = g x), \mathit{expect} n p j f = \mathit{expect} n p j g$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.10 (Expect const).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (c: E), (\mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => c) = c$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.11 (Expect mono).**

$$\forall (n: \mathbb{N}), \forall (j: \mathbb{N}), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (f: \mathbb{N} \to \mathbb{R}), \forall (g: \mathbb{N} \to \mathbb{R}), \forall (h: \forall x \leq j, x \leq n \to f x \leq g x), \mathit{expect} n p j f \leq \mathit{expect} n p j g$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.12 (Expect smul).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (c: \mathbb{R}), \forall (f: \mathbb{N} \to E), (\mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => c \cdot f x) = c \cdot \mathit{expect} n p j f$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.13 (Expect succ).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (f: \mathbb{N} \to E), \mathit{expect} n p (j + 1) f = \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => (1 - q n p \mathit{val} x) \cdot f x + q n p \mathit{val} x \cdot f (x + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.14 (Expect zero time).**

$$\forall (E: \mathit{Type}), [\mathit{AddCommMonoid} E] [\mathrm{anonymous}\mathit{root}\mathrm{anonymous}.\mathit{Module} \mathbb{R} E] \forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (f: \mathbb{N} \to E), \mathit{expect} n p 0 f = f 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_zero_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.15 (Insert Throw).**

$$\forall (n: \mathbb{N}), \forall (s: \mathit{Finset} (\mathit{Fin} n)), \forall (a: \mathit{Option} (\mathit{Fin} n)), (\mathit{insertThrow} n s a : \mathit{Finset} (\mathit{Fin} n)) = \mathit{match} x \mathit{with} | \mathit{none} => s | \mathit{some} x => \mathit{insert} x s$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.insertThrow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.16 (Mean).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), (\mathit{mean} n p j : \mathbb{R}) = \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => \mathit{val} x$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.17 (Mean bounds).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), 0 \leq \mathit{mean} n p j \land \mathit{mean} n p j \leq \mathit{val} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.18 (Mean succ).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \mathit{mean} n p (j + 1) = a n p \cdot \mathit{mean} n p j + p$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.19 (Occupied).**

$$\forall (n: \mathbb{N}), \forall (j: \mathbb{N}), \forall (a: \mathit{DiscardedOccupancy}.\mathit{History} n j), (\mathit{occupied} n j a : \mathit{Finset} (\mathit{Fin} n)) = \mathit{Nat}.\mathit{brecOn} (\mathit{motive} := \mathit{fun} (x : \mathbb{N}) => \mathit{DiscardedOccupancy}.\mathit{History} n x \to \mathit{Finset} (\mathit{Fin} n)) \mathit{xOne} (\mathit{occupied}.\mathrm{anonymous}f n) x$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.20 (Q).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (x: \mathbb{R}), (q n p x : \mathbb{R}) = p \cdot (1 - x / \mathit{val} n)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.21 (Q bounds).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (x: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hx}: 0 \leq x), \forall (\mathit{hx}': x \leq \mathit{val} n), 0 \leq q n p x \land q n p x \leq p$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.q_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.22 (Throw Mass).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (a: \mathit{Option} (\mathit{Fin} n)), (\mathit{throwMass} n p a : \mathbb{R}) = \mathit{match} x \mathit{with} | \mathit{none} => 1 - p | \mathit{some} \mathit{val} => p / \mathit{val} n$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.throwMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.23 (V).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (x: \mathbb{R}), (v n p x : \mathbb{R}) = q n p x \cdot (1 - q n p x)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.24 (V bounds).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (x: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (\mathit{hx}: 0 \leq x), \forall (\mathit{hx}': x \leq \mathit{val} n), 0 \leq v n p x \land v n p x \leq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.v_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.25 (Variance).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), (\mathit{variance} n p j : \mathbb{R}) = \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => (\mathit{val} x - \mathit{mean} n p j) ^ 2$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.26 (Variance le time).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \mathit{variance} n p j \leq \mathit{val} j$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_le_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.27 (Variance nonneg).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), 0 \leq \mathit{variance} n p j$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.28 (Weighted variance).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (p: \mathbb{R}), \forall (m: \mathbb{N}), \mathit{variance} n p m = \sum j \in \mathit{Finset}.\mathit{range} m, (a n p ^ (m - (j + 1))) ^ 2 \cdot \mathit{expect} n p j \mathit{fun} (x : \mathbb{N}) => v n p \mathit{val} x$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.weighted_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.29 (Word Mass).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (j: \mathbb{N}), \forall (\omega: \mathit{DiscardedOccupancy}.\mathit{History} n j), (\mathit{wordMass} n p j \omega : \mathbb{R}) = \prod i : \mathit{Fin} j, \mathit{throwMass} n p (\omega i)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.wordMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.30 (Word Mass nonneg).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (\mathit{hp}: 0 \leq p), \forall (\mathit{hpUpper}: p \leq 1), \forall (j: \mathbb{N}), \forall (\omega: \mathit{DiscardedOccupancy}.\mathit{History} n j), 0 \leq \mathit{wordMass} n p \omega$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.wordMass_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

## References

- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.History`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.a`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.a_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.average`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.count`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_add`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_congr`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_const`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_mono`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_smul`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_succ`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_zero_time`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.insertThrow`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean_succ`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.occupied`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.q`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.q_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.throwMass`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.v`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.v_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_le_time`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_lower`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_nonneg`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.weighted_variance`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.wordMass`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.wordMass_nonneg`
