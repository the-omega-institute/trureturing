# The Two-Parameter Greedy Three-Sumfree Characterization

## Abstract

Greedy three-sumfree membership has a universal two-parameter periodic formula.

This repository proof establishes Conjecture 17 as printed on page 18 of Bosma, Bruin, Fokkink, Grube, Reuijl and Tromp, Using Walnut to Solve Problems from the OEIS, Journal of Integer Sequences 28 (2025), Article 25.3.8 (arXiv:2503.04122). The source states a conjecture, not a prior proof. Shtrezi's arXiv:2606.17447 treats the different third seed g+1, Conjecture 16. All nine declarations below are derived here; these citations identify scope.

Every integer variable is natural. Subtraction is truncated at zero, mod is the natural-number remainder, Icc is the inclusive natural interval, union is set union, image is direct image, and an indexed union binds its natural index. A set used as a predicate means membership in that set.

**Definition 1.1 (Restricted sums of three distinct entries).**

$$\forall P: (\mathbb{N} \to \operatorname{Prop}), z: \mathbb{N}, \operatorname{RestrictedThreeSum}\left(P, z\right) \Leftrightarrow \exists x, y, w: \mathbb{N}, (x < y \land y < w \land P\left(x\right) \land P\left(y\right) \land P\left(w\right) \land x + y + w = z).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.RestrictedThreeSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strict inequalities order three different entries. The definition does not assume they precede their sum; positivity supplies that fact on the candidate set when comparing it with the greedy rule.

**Definition 1.2 (The initial interval and translated periodic intervals).**

$$\forall g, d: \mathbb{N},\operatorname{A}\left(g, d\right) = \operatorname{union}\left(\operatorname{union}\left(\left\{1, g\right\}, \operatorname{Icc}\left(g + d, 2 \cdot g + d\right)\right), \operatorname{union}_{t \ge 1} \operatorname{image}\left((r \mapsto t \cdot \left(5 \cdot g + 2 \cdot d\right) + r), \operatorname{Icc}\left(g + d - 2, 2 \cdot g + d - 2\right)\right)\right).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the stated union expression itself: the two isolated seeds, the closed initial interval, and every translate with t at least one. The translation function sends r to t times the modulus plus r.

**Definition 1.3 (Literal least-next-entry greedy prefixes).**

$$\forall g, d: \mathbb{N},\operatorname{greedyPrefix}\left(g, d, 0\right) = [g + d, g, 1] \land (\forall n: \mathbb{N}, \operatorname{greedyPrefix}\left(g, d, n + 1\right) = \operatorname{cons}\left(\min \{z \in \mathbb{N} \mid \operatorname{headD}\left(\operatorname{greedyPrefix}\left(g, d, n\right), 0\right) < z \land \neg (\exists x, y, w: \mathbb{N}, (x < y \land y < w \land x \in \operatorname{greedyPrefix}\left(g, d, n\right) \land y \in \operatorname{greedyPrefix}\left(g, d, n\right) \land w \in \operatorname{greedyPrefix}\left(g, d, n\right) \land x + y + w = z))\}, \operatorname{greedyPrefix}\left(g, d, n\right)\right)).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.greedyPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prefixes are stored in reverse order, so the head is the most recent entry; headD has default zero. The minimum is Nat.find applied to the displayed predicate. Its existence follows by taking a number above three times the sum of the list and its head. Thus the recurrence is total, and for the theorem's parameters it generates the increasing sequence starting with 1, g, g+d. No periodic formula enters this definition.

**Definition 1.4 (Membership in the greedy sequence).**

$$\forall g, d, z: \mathbb{N},\operatorname{S}\left(g, d, z\right) \Leftrightarrow \exists n: \mathbb{N}, z \in \operatorname{greedyPrefix}\left(g, d, n\right).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An integer occurs if it belongs to some generated prefix. A private induction identifies these prefixes with an independent scan through successive natural numbers, which obeys the greedy membership recurrence.

**Theorem 1.5 (Coverage of the complete initial gap).**

$$\begin{aligned}\forall g, d, z: \mathbb{N},\\(2 \le d \land d + 1 \le g) \implies \\(2 \cdot g + d < z \land z < (5 \cdot g + 2 \cdot d) + (g + d - 2)) \implies \\\operatorname{RestrictedThreeSum}\left(\operatorname{A}\left(g, d\right), z\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.initial_gap_covered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The construction uses (1+g)+I(0), one plus a distinct pair from I(0), g plus a distinct pair from I(0), and a distinct triple from I(0), where I(0)=Icc(g+d,2g+d). The last family covers the remaining interval from M through M+a-1, with M=5g+2d and a=g+d-2. It is the fourth initial family recorded in witness version two.

**Theorem 1.6 (Coverage of every periodic gap).**

$$\begin{aligned}\forall g, d, t, z: \mathbb{N},\\(2 \le d \land d + 1 \le g) \implies 1 \le t \implies \\(t \cdot \left(5 \cdot g + 2 \cdot d\right) + (2 \cdot g + d - 2) < z \land z < t \cdot \left(5 \cdot g + 2 \cdot d\right) + (5 \cdot g + 2 \cdot d) + (g + d - 2)) \implies \\\operatorname{RestrictedThreeSum}\left(\operatorname{A}\left(g, d\right), z\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.periodic_gap_covered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t at least one, write I(t)=tM+Icc(a,b), M=5g+2d, a=g+d-2, b=2g+d-2. The four families are (1+g)+I(t), 1+I(0)+I(t), g+I(0)+I(t), and a distinct pair from I(0) plus I(t). Interval-sum existence uses Set.Icc_add_Icc; explicit pair constructions and the parameter inequalities establish the overlaps and distinctness.

**Theorem 1.7 (The exact restricted-sum complement).**

$$\begin{aligned}\forall g, d, z: \mathbb{N},\\(2 \le d \land d + 1 \le g) \implies \\(\operatorname{RestrictedThreeSum}\left(\operatorname{A}\left(g, d\right), z\right) \Leftrightarrow (g + d < z \land \neg (z \in \operatorname{A}\left(g, d\right)))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.restricted_three_sum_eq_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both gap-coverage theorems are used in the complement-to-sum direction. Conversely, residue bounds exclude all candidate triple sums from A, including the exceptional initial endpoints. This identity is used on the live path to the characterization.

**Theorem 1.8 (The full published characterization).**

$$\begin{aligned}\forall g, d, z: \mathbb{N},\\(2 \le d \land d + 1 \le g) \implies \\(\operatorname{S}\left(g, d, z\right) \Leftrightarrow (z = 1 \lor z = g \lor z = 2 \cdot g + d - 1 \lor z = 2 \cdot g + d \lor (g + d \le z \land g + d - 2 \le z \bmod \left(5 \cdot g + 2 \cdot d\right) \land z \bmod \left(5 \cdot g + 2 \cdot d\right) \le 2 \cdot g + d - 2))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.conjecture17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sumset identity proves that the candidate satisfies the greedy rule. Strong induction gives uniqueness of that rule, and the prefix-scan invariant transfers it to the literal least-next-entry sequence. The four exceptions and the non-strict cutoff z at least g+d agree with the published version. The result is universal in both parameters; finite prefix checks are anonymous fidelity examples, not separate certificates.

**Theorem 1.9 (The greedy sequence equals the interval candidate).**

$$\forall g, d: \mathbb{N},(2 \le d \land d + 1 \le g) \implies (\operatorname{S}\left(g, d\right) = \operatorname{A}\left(g, d\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.s_eq_A` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pointwise characterization and the candidate's residue description give equality of the two predicates by function extensionality.

## References

- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.A`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.RestrictedThreeSum`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.S`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.conjecture17`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.greedyPrefix`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.initial_gap_covered`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.periodic_gap_covered`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.restricted_three_sum_eq_complement`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter.s_eq_A`
