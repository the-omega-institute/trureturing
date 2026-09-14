# Index Divisibility for Vanishing Diagonals

## Abstract

Normalized vanishing diagonals inherit index-power divisibility from their exponents.

The note hanna2016diagonalindex quotes Hanna's A266489, A300732, A300733, A292394, and A300734. The normalized family has constant and linear coefficients one and vanishing diagonals in degrees n>1. The NAMEs of A300732 and A300733 print n>=1, which contradicts their published linear coefficient one. Their instances below use the consistent n>1 interpretation; the literal quotations remain in the note.

The function e maps natural numbers to natural numbers. Indices n, m, j, depths d, and the divisibility exponent k are natural. Write A(e) for generatingSeries(e), P(e,d) for the integer-series approximation, and frozen(p,n) for NegativePowerDiagonalModPrime.a(p,n). All series have integer coefficients. The operator intCast embeds a natural number in the integers. Divisibility in the exponent hypothesis is natural divisibility; divisibility of coefficients is integer divisibility.

The operators coeff, mk, subst, and invOfUnit are the Lean power-series operations. For a normalized series, invOfUnit(A,1) is its formal inverse, so subst(A,X*invOfUnit(A,1)^e(n)) means A(x/A(x)^e(n)). In the engine identity U is a unit, val forgets its unit structure, and N is an arbitrary integer, including negative values. Subtraction in a coefficient index is natural subtraction; subtraction from N is integer subtraction.

**Definition 1.1 (The triangular coefficient construction).**

$$\begin{aligned}\forall e: \mathbb{N} \longrightarrow \mathbb{N}, \operatorname{P}\left(e, 0\right) = 1\\\forall e: \mathbb{N} \longrightarrow \mathbb{N}, \forall d: \mathbb{N}, \operatorname{P}\left(e, d + 1\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (n \le 1) \operatorname{then} 1 \operatorname{else} -(\sum_{j \in \operatorname{range}\left(n\right)} ((\operatorname{coeff}\left(j, \operatorname{P}\left(e, d\right)\right)) \cdot (\operatorname{coeff}\left(n - j, (\operatorname{invOfUnit}\left(\operatorname{P}\left(e, d\right), 1\right))^{(e\left(n\right)) \cdot (j)}\right)))))\right)\\\forall e: \mathbb{N} \longrightarrow \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(e, n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(e, n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The update fixes degrees zero and one at one. At every higher degree it negates the sum over smaller outer degrees. The degree-zero summand vanishes, and every positive outer degree leaves a strictly smaller degree in the inverse power. Each update therefore improves agreement by one degree, making the indicated coefficients stable.

**Definition 1.2 (The generating series).**

$$\forall e: \mathbb{N} \longrightarrow \mathbb{N}, \operatorname{A}\left(e\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{a}\left(e, n\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stabilized integer coefficients define A(e).

**Theorem 1.3 (The normalized vanishing-diagonal equation).**

$$\forall e: \mathbb{N} \longrightarrow \mathbb{N}, (\operatorname{coeff}\left(0, \operatorname{A}\left(e\right)\right) = 1) \land ((\operatorname{coeff}\left(1, \operatorname{A}\left(e\right)\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{A}\left(e\right), (X) \cdot ((\operatorname{invOfUnit}\left(\operatorname{A}\left(e\right), 1\right))^{e\left(n\right)})\right)\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the substitution through outer degree n gives a(e,n) plus the finite sum used in the update. The fixed-point identity thus proves the displayed functional equation, with both normalization conditions.

**Theorem 1.4 (Uniqueness).**

$$\forall e: \mathbb{N} \longrightarrow \mathbb{N}, \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{coeff}\left(0, B\right) = 1) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, \operatorname{subst}\left(B, (X) \cdot ((\operatorname{invOfUnit}\left(B, 1\right))^{e\left(n\right)})\right)\right) = 0)) \implies (B = \operatorname{A}\left(e\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized equation is equivalent to the triangular fixed-point condition. The inverse-difference identity preserves coefficient agreement, and the update increases its degree. Induction identifies every normalized solution B with A(e).

**Theorem 1.5 (The integer-power engine).**

$$\forall U: \operatorname{Units}\left(\operatorname{PowerSeries}\left(\mathbb{Z}\right)\right), \forall N: \mathbb{Z}, \forall j: \mathbb{N}, (0 < j) \implies ((\operatorname{intCast}\left(j\right)) \cdot (\operatorname{coeff}\left(j, \operatorname{val}\left((U)^{N}\right)\right)) = (N) \cdot (\operatorname{coeff}\left(j - 1, (\operatorname{val}\left((U)^{N - 1}\right)) \cdot (\operatorname{derivative}\left(\mathbb{Z}, \operatorname{val}\left(U\right)\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.power_coefficient_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the formal derivative to integer powers of a unit. Multiplying by U handles the successor step; cancellation by the same unit handles the predecessor step. Extracting degree j-1 gives the identity for every integer N. In particular, N divides j times the coefficient.

**Theorem 1.6 (The general index-power theorem).**

$$\forall e: \mathbb{N} \longrightarrow \mathbb{N}, \forall k: \mathbb{N}, (\forall n: \mathbb{N}, (n)^{k} \mid e\left(n\right)) \implies (\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{intCast}\left(n\right))^{k} \mid \operatorname{a}\left(e, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.index_power_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction reduces the result to each smaller-degree summand. For each prime p, put alpha=v_p(n). If v_p(m)<alpha, then v_p(n-m)=v_p(m). The engine applied to the inverse series with exponent e(n)*m forces its coefficient to contain p^(k*alpha). If v_p(m)>=alpha, the induction hypothesis supplies that factor in a(e,m). Prime factorization assembles these factors into n^k, and divisibility survives the finite sum and its negation.

**Theorem 1.7 (A300732: index divisibility).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{intCast}\left(n\right) \mid \operatorname{a}\left((m: \mathbb{N} \mapsto (2) \cdot (m)), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300732` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a300732-diagonal-index-divisibility` (proved) by `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300732`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a300732-diagonal-index-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300732","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2016). *OEIS A266489, A300732, A300733, A292394, and A300734: vanishing-diagonal index divisibility*. URL: <https://oeis.org/A266489>.

*Commentary.*

Use e(m)=2*m and k=1 in the normalized family. The interpretation of the source's degree-one boundary is stated above.

**Theorem 1.8 (A300733: index divisibility).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{intCast}\left(n\right) \mid \operatorname{a}\left((m: \mathbb{N} \mapsto (3) \cdot (m)), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300733` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a300733-diagonal-index-divisibility` (proved) by `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300733`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a300733-diagonal-index-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300733","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2016). *OEIS A266489, A300732, A300733, A292394, and A300734: vanishing-diagonal index divisibility*. URL: <https://oeis.org/A266489>.

*Commentary.*

Use e(m)=3*m and k=1 in the normalized family. The interpretation of the source's degree-one boundary is stated above.

**Theorem 1.9 (A292394: square-index divisibility).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{intCast}\left(n\right))^{2} \mid \operatorname{a}\left((m: \mathbb{N} \mapsto (m)^{2}), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a292394` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a292394-diagonal-index-divisibility` (proved) by `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a292394`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a292394-diagonal-index-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a292394","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2016). *OEIS A266489, A300732, A300733, A292394, and A300734: vanishing-diagonal index divisibility*. URL: <https://oeis.org/A266489>.

*Commentary.*

Use e(m)=m^2 and k=2. The exponent-divisibility hypothesis is reflexive.

**Theorem 1.10 (A300734: square-index divisibility).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{intCast}\left(n\right))^{2} \mid \operatorname{a}\left((m: \mathbb{N} \mapsto (2) \cdot ((m)^{2})), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300734` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a300734-diagonal-index-divisibility` (proved) by `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300734`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a300734-diagonal-index-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300734","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2016). *OEIS A266489, A300732, A300733, A292394, and A300734: vanishing-diagonal index divisibility*. URL: <https://oeis.org/A266489>.

*Commentary.*

Use e(m)=2*m^2 and k=2. Every square m^2 divides this exponent.

**Theorem 1.11 (Agreement with the frozen A266489 object).**

$$\forall n: \mathbb{N}, \operatorname{a}\left((m: \mathbb{N} \mapsto m), n\right) = \operatorname{frozen}\left(2, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.agreement_a266489` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p=2 and n>1, the frozen exponent (p-1)*(n-1)+1 equals n. NegativePowerDiagonalModPrime.generating_unique identifies the two normalized series. Coefficient extraction gives agreement at every degree.

**Theorem 1.12 (A266489: clause C1 on the frozen object).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{intCast}\left(n\right) \mid \operatorname{frozen}\left(2, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a266489` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a266489-diagonal-index-divisibility` (proved) by `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a266489`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a266489-diagonal-index-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a266489","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2016). *OEIS A266489, A300732, A300733, A292394, and A300734: vanishing-diagonal index divisibility*. URL: <https://oeis.org/A266489>.

*Commentary.*

The general theorem with e(m)=m and k=1 gives index divisibility. The agreement lemma transfers it to the frozen coefficient function, proving clause C1 on that existing object.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.a`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.agreement_a266489`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a266489`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a292394`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300732`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300733`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.hanna_conjecture_a300734`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.index_power_divisibility`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.power_coefficient_identity`
- Dependency: [D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime](NegativePowerDiagonalModPrime.md)
