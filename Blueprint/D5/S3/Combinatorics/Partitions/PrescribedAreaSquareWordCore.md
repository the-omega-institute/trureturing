# Prescribed-area square word core

## Abstract

Literal expansion, ordered base-eight source blocks and exact-area square words with a common joint moment image.

**Definition 1.1 (Level-three Boolean indices).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.level3Index`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.level3Index` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index is the function with values x,y,z on Fin 3. True denotes a and false denotes b.

**Definition 1.2 (The first P source).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.P0`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.P0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P0 is the positivePairWords second component at index (true,false,true), the literal baaab.

**Definition 1.3 (The second P source).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.P1`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.P1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P1 is the first component at that same index, the literal ababa.

**Definition 1.4 (The first Q source).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.Q0`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.Q0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q0 is the second component at index (true,false,false), the literal babab.

**Definition 1.5 (The second Q source).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.Q1`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.Q1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q1 is the first component at that same index, the literal abbba.

**Definition 1.6 (The four selected blocks).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.H`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(e,f) is P_e followed by Q_f,Q0,P0. Its counts are (10,10), its scattered ab area is 50, and its G coordinates are (10,10,0,−92−24e−12f,−136−12e−24f), with Boolean values represented by zero or one.

**Theorem 1.7 (Rows of the actual repeated word).**

$$\forall n \in \mathbb{N}, \forall w \in \operatorname{List}\left(Bool\right), \operatorname{rows}\left(\operatorname{literalPowerWord}\left(n, w\right)\right) = \operatorname{flatMap}\left(\operatorname{rows}\left(w\right), \operatorname{fun}\left(r, \operatorname{replicate}\left(n, n \times r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.rows_literalPowerWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual row is repeated n times and multiplied by n. The identity includes n=0 and the empty word.

**Theorem 1.8 (Homogeneity of the actual fan).**

$$\forall n \in \mathbb{N}, \forall w \in \operatorname{List}\left(Bool\right), \operatorname{G}\left(\operatorname{literalPowerWord}\left(n, w\right)\right) = \operatorname{Five}\left(n \times \operatorname{u}\left(\operatorname{G}\left(w\right)\right), n \times \operatorname{v}\left(\operatorname{G}\left(w\right)\right), (n)^{2} \times \operatorname{d}\left(\operatorname{G}\left(w\right)\right), (n)^{3} \times \operatorname{e}\left(\operatorname{G}\left(w\right)\right), (n)^{3} \times \operatorname{f}\left(\operatorname{G}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.G_literalPowerWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row identity scales area quadratically and both the square-row and odd-row sums cubically. The existing actual fan formulas then give all five homogeneous coordinates.

**Definition 1.9 (Dyadic radix).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.q`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(J)=2^J.

**Definition 1.10 (Core side).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.coreSide`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.coreSide` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coreSide(J)=70(q(J)−1), an even natural number.

**Definition 1.11 (The full core index domain).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.CoreIndex`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.CoreIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CoreIndex(J)=Fin(q(J)^3) × Fin(q(J)^3).

**Definition 1.12 (The actual ordered core).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.V`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use Nat.digitsAppend 8 J for both coordinates. In increasing scale i, concatenate the seven thresholds ℓ=1,…,7 of H(ℓ≤d_i,ℓ≤e_i), with each letter repeated 2^i times. For J=0 this is an auxiliary empty word contribution; it is not a native empty tree.

**Definition 1.13 (The exact quotient/remainder suffix).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.fixedZ`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.fixedZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b>0 and 0≤κ≤b², let j=κ/b and z=κ mod b. At z=0 use b^(b−j)a^b b^j; otherwise use b^(b−j−1)a^z b a^(b−z)b^j. Its direct rows are j copies of b, followed when z>0 by z, followed by the required zero padding. The exponent guards include κ=0 and κ=b².

**Definition 1.14 (Suffix area).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.suffixArea`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.suffixArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

suffixArea(J,h,t)=t+coreSide(J)²/2−coreSide(J)h in natural arithmetic. The square hypotheses prove nontruncation and the upper bound (h−coreSide(J))² before this subtraction is used.

**Definition 1.15 (The completed square word).**

Lean statement: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.W`

*Formalization.* `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(J,h,t,x)=V(J,x) followed by fixedZ(h−coreSide(J),suffixArea(J,h,t)). The suffix is fixed across the full core index domain.

**Theorem 1.16 (Exact area and simultaneous joint injection).**

$$\forall J \in \mathbb{N}, \forall h \in \mathbb{N}, \forall t \in \mathbb{N}, (0 < h) \land (8 \times \operatorname{coreSide}\left(J\right) \leq h) \land ((h)^{2} \leq 8 \times t) \land (8 \times t \leq 7 \times (h)^{2}) \implies (\forall x \in \operatorname{CoreIndex}\left(J\right), (\operatorname{G}\left(\operatorname{V}\left(J, x\right)\right) = \operatorname{Five}\left(\operatorname{coreSide}\left(J\right), \operatorname{coreSide}\left(J\right), 0, -92 \times ((\operatorname{q}\left(J\right))^{3} - 1) - 24 \times \operatorname{val}\left(\operatorname{fst}\left(x\right)\right) - 12 \times \operatorname{val}\left(\operatorname{snd}\left(x\right)\right), -136 \times ((\operatorname{q}\left(J\right))^{3} - 1) - 12 \times \operatorname{val}\left(\operatorname{fst}\left(x\right)\right) - 24 \times \operatorname{val}\left(\operatorname{snd}\left(x\right)\right)\right)) \land (\operatorname{count}\left(\operatorname{V}\left(J, x\right), true\right) = \operatorname{coreSide}\left(J\right)) \land (\operatorname{count}\left(\operatorname{V}\left(J, x\right), false\right) = \operatorname{coreSide}\left(J\right)) \land (\operatorname{scatteredTrueFalseCount}\left(\operatorname{V}\left(J, x\right)\right) = \frac{(\operatorname{coreSide}\left(J\right))^{2}}{2})) \land ((0 < h - \operatorname{coreSide}\left(J\right)) \land (\operatorname{Even}\left(\operatorname{coreSide}\left(J\right)\right)) \land (\operatorname{coreSide}\left(J\right) \times h \leq t + \frac{(\operatorname{coreSide}\left(J\right))^{2}}{2}) \land (\operatorname{suffixArea}\left(J, h, t\right) + \operatorname{coreSide}\left(J\right) \times h = t + \frac{(\operatorname{coreSide}\left(J\right))^{2}}{2}) \land (\operatorname{suffixArea}\left(J, h, t\right) \leq (h - \operatorname{coreSide}\left(J\right))^{2})) \land (\forall x \in \operatorname{CoreIndex}\left(J\right), (\operatorname{W}\left(J, h, t, x\right) \in \operatorname{wordFiber}\left(h, h, t\right)) \land (\operatorname{count}\left(\operatorname{W}\left(J, h, t, x\right), true\right) = h) \land (\operatorname{count}\left(\operatorname{W}\left(J, h, t, x\right), false\right) = h) \land (\operatorname{scatteredTrueFalseCount}\left(\operatorname{W}\left(J, h, t, x\right)\right) = t) \land (\operatorname{length}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right) = h) \land (\operatorname{SortedGE}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right)) \land (\forall r \in \operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right), r \leq h) \land (\operatorname{sum}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right) = t) \land (\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right) = \operatorname{append}\left(\operatorname{map}\left(\operatorname{rows}\left(\operatorname{fixedZ}\left(h - \operatorname{coreSide}\left(J\right), \operatorname{suffixArea}\left(J, h, t\right)\right)\right), \operatorname{fun}\left(r, r + \operatorname{coreSide}\left(J\right)\right)\right), \operatorname{rows}\left(\operatorname{V}\left(J, x\right)\right)\right)) \land (\operatorname{G}\left(\operatorname{W}\left(J, h, t, x\right)\right) = \operatorname{Five}\left(h, h, 2 \times t - (h)^{2}, -92 \times ((\operatorname{q}\left(J\right))^{3} - 1) - 24 \times \operatorname{val}\left(\operatorname{fst}\left(x\right)\right) - 12 \times \operatorname{val}\left(\operatorname{snd}\left(x\right)\right) + \operatorname{e}\left(\operatorname{G}\left(\operatorname{fixedZ}\left(h - \operatorname{coreSide}\left(J\right), \operatorname{suffixArea}\left(J, h, t\right)\right)\right)\right) + 3 \times \operatorname{coreSide}\left(J\right) \times \operatorname{d}\left(\operatorname{G}\left(\operatorname{fixedZ}\left(h - \operatorname{coreSide}\left(J\right), \operatorname{suffixArea}\left(J, h, t\right)\right)\right)\right), -136 \times ((\operatorname{q}\left(J\right))^{3} - 1) - 12 \times \operatorname{val}\left(\operatorname{fst}\left(x\right)\right) - 24 \times \operatorname{val}\left(\operatorname{snd}\left(x\right)\right) + \operatorname{f}\left(\operatorname{G}\left(\operatorname{fixedZ}\left(h - \operatorname{coreSide}\left(J\right), \operatorname{suffixArea}\left(J, h, t\right)\right)\right)\right) + 3 \times \operatorname{coreSide}\left(J\right) \times \operatorname{d}\left(\operatorname{G}\left(\operatorname{fixedZ}\left(h - \operatorname{coreSide}\left(J\right), \operatorname{suffixArea}\left(J, h, t\right)\right)\right)\right)\right))) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{CoreIndex}\left(J\right), \operatorname{W}\left(J, h, t, x\right)\right)\right)) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{CoreIndex}\left(J\right), \operatorname{Pair}\left(\operatorname{e}\left(\operatorname{G}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right), \operatorname{f}\left(\operatorname{G}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right)\right)\right)\right)) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{CoreIndex}\left(J\right), \operatorname{Pair}\left(\operatorname{squareRows}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right), \operatorname{oddRows}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right)\right)\right)\right)) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{CoreIndex}\left(J\right), \operatorname{W}\left(J, h, t, x\right)\right)\right)\right) = (\operatorname{q}\left(J\right))^{6}) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{CoreIndex}\left(J\right), \operatorname{Pair}\left(\operatorname{e}\left(\operatorname{G}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right), \operatorname{f}\left(\operatorname{G}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right)\right)\right)\right)\right) = (\operatorname{q}\left(J\right))^{6}) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{CoreIndex}\left(J\right), \operatorname{Pair}\left(\operatorname{squareRows}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right), \operatorname{oddRows}\left(\operatorname{rows}\left(\operatorname{W}\left(J, h, t, x\right)\right)\right)\right)\right)\right)\right) = (\operatorname{q}\left(J\right))^{6}) \land ((\operatorname{q}\left(J\right))^{6} \leq \operatorname{capacity}\left(h, h, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.square_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural J,h,t with h>0, 8a≤h and h²≤8t≤7h², the actual words have counts (h,h), area exactly t and h sorted direct rows bounded by h. Membership in wordFiber includes nonemptiness. The core has zero D, while the completed square has D=2t−h². Concatenation translates the suffix rows by a and adds the fixed moment vector (E_Z+3aD_Z,F_Z+3aD_Z). For μ=rows(W), the direct fan formulas give E=h³−6ht+6 squareRows(μ) and F=−h³+6ht−6 oddRows(μ); the latter statistic is the square-column sum of the same Ferrers diagram. The independent core directions (−24,−12) and (−12,−24) have determinant 432. Consequently the same actual word supplies both moments, and its squareRows and oddRows pair is also injective. Each of the word, joint fan and joint row-statistic images has exactly q^6 elements, giving that lower bound in the existing whole word-fiber capacity. J=0 is included. The direct area t is preserved even above h²/2, without reversing the core.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.CoreIndex`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.G_literalPowerWord`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.H`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.P0`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.P1`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.Q0`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.Q1`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.V`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.W`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.coreSide`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.fixedZ`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.level3Index`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.q`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.rows_literalPowerWord`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.square_family`
- Truth anchor: `D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.suffixArea`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution](../../../S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution.md)
- Dependency: [D5/S3/Combinatorics/Partitions/WordPartitionInverse](WordPartitionInverse.md)
