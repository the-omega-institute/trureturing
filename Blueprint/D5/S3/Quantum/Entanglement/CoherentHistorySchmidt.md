# Coherent History Schmidt Rank

## Abstract

Uniform fixed-occupation word states have exact cut ranks and positive binomial Schmidt weights.

A is any finite alphabet with decidable equality. Words are functions Fin n to A; a is the total occupation multiset, and card(a)=t+s specifies the cut. B(a,t) denotes Boundary(a,t), the finite type of multisets b with b<=a and card(b)=t. val forgets this subtype. M(n,b) counts the actual words of length n with occupation b. V(n,b,w) is their normalized uniform vector, evaluated at w. C(a,t,s) denotes coefficientMatrix over the complex numbers. Matrix.rank is the complex dimension of the range of its multiplication linear map. This supplies the decomposition and rank clauses of the coherent-history atom; its fixed-register pure-state circuit clause remains open.

**Theorem 1.1 (Legal concatenations select a feasible occupation boundary).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall u \in Word\left(A, t\right),\; \forall v \in Word\left(A, s\right),\; occupation\left(\operatorname{Fin.append}\left(u, v\right)\right) = a \Leftrightarrow \left(\exists b \in Boundary\left(a, t\right),\; occupation\left(u\right) = val\left(b\right) \land occupation\left(v\right) = a - val\left(b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.legal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

A concatenation has total occupation a exactly when its prefix occupation is a feasible boundary and its suffix occupation is the complementary multiset.

**Theorem 1.2 (Coefficients come from the full uniform word state).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall u \in Word\left(A, t\right),\; \forall v \in Word\left(A, s\right),\; C\left(a, t, s, u, v\right) = V\left(t + s, a, FinAppend\left(u, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_eq_uniform_word` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Thus the coefficient is 1/sqrt(M(t+s,a)) exactly on legal concatenations, and zero otherwise. The full word vector has norm one when card(a)=t+s.

**Theorem 1.3 (The matrix factors through feasible sectors).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; C\left(a, t, s\right) = prefixIncidence\left(a, t\right) \cdot suffixAmplitude\left(a, t, s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_factorization` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The prefix incidence is one exactly when occupation(u)=val(b). The suffix amplitude is 1/sqrt(M(t+s,a)) exactly when occupation(v)=a-val(b). Both are zero elsewhere. This factorization bounds rank by the sector count.

**Theorem 1.4 (Actual representative words give a full diagonal restriction).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall h \in card\left(a\right) = t + s,\; submatrix\left(C\left(a, t, s\right), prefixRepresentative\left(a, t\right), suffixRepresentative\left(h\right)\right) = diagonal\left(b:B\left(a, t\right) \mapsto historyAmplitude\left(a, t + s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_diagonal_restriction` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Each row and column is chosen by listing its prescribed occupation. The restriction is diagonal with the nonzero full-history amplitude on every diagonal entry. Its rank supplies the lower bound for the full coefficient matrix.

**Theorem 1.5 (Every cut rank equals the feasible boundary count).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow rank\left(C\left(a, t, s\right)\right) = card\left(boundaries\left(a, t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_rank` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The theorem concerns the entire rectangular word matrix. In particular t=0 and s=0 are allowed. Setting s=card(a)-t yields every valid cut.

**Theorem 1.6 (Every Schmidt coefficient is positive).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow \left(\forall b \in B\left(a, t\right),\; 0 < schmidtCoefficient\left(a, t, s, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_pos` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The coefficient is sqrt(M(t,val(b))) times sqrt(M(s,a-val(b))) divided by sqrt(M(t+s,a)). All three word fibers contain explicitly constructed representatives.

**Theorem 1.7 (Squared coefficients are multiplicity ratios).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall b \in B\left(a, t\right),\; schmidtCoefficient\left(a, t, s, b\right)^{2} = \frac{M\left(t, val\left(b\right)\right) \cdot M\left(s, a - val\left(b\right)\right)}{M\left(t + s, a\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_sq` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The displayed multiplicities are actual finite word-fiber cardinalities. The following binomial identity uses their universal multinomial counting formula.

**Theorem 1.8 (Squared coefficients are binomial weights).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow \left(\forall b \in B\left(a, t\right),\; schmidtCoefficient\left(a, t, s, b\right)^{2} = \frac{\prod_{z:A}{choose\left(count\left(a, z\right), count\left(val\left(b\right), z\right)\right)}}{choose\left(t + s, t\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_sq_binomial` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Each coordinate binomial coefficient and the denominator are natural numbers canonically included in the reals. The product runs over every symbol in A, including zero occupation coordinates. The proof uses actual prefix, suffix, and full word cardinalities and cancels positive factorial products. No counting identity is assumed, and both endpoint cuts are included.

**Theorem 1.9 (The Schmidt coefficient is the positive square root).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow \left(\forall b \in B\left(a, t\right),\; schmidtCoefficient\left(a, t, s, b\right) = sqrt\left(\frac{\prod_{z:A}{choose\left(count\left(a, z\right), count\left(val\left(b\right), z\right)\right)}}{choose\left(t + s, t\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_eq_sqrt_binomial` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

sqrt is the nonnegative real square root. Positivity of the existing coefficient selects that root, identifying the coefficient in the normalized decomposition.

**Theorem 1.10 (Normalized occupation-sector decomposition).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow \left(\forall u \in Word\left(A, t\right),\; \forall v \in Word\left(A, s\right),\; C\left(a, t, s, u, v\right) = \sum_{b:B\left(a, t\right)}{ofReal\left(schmidtCoefficient\left(a, t, s, b\right)\right) \cdot V\left(t, val\left(b\right), u\right) \cdot V\left(s, a - val\left(b\right), v\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.normalized_coefficient_factorization` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The equality is coordinatewise on every actual prefix and suffix word. ofReal is the canonical inclusion of the real positive coefficient into the complex numbers.

**Theorem 1.11 (Both sides are orthonormal).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow \left(\forall b \in B\left(a, t\right),\; \forall c \in B\left(a, t\right),\; \sum_{u:Word\left(A, t\right)}{star\left(V\left(t, val\left(b\right), u\right)\right) \cdot V\left(t, val\left(c\right), u\right)} = ite\left(b = c, 1, 0\right) \land \sum_{v:Word\left(A, s\right)}{star\left(V\left(s, a - val\left(b\right), v\right)\right) \cdot V\left(s, a - val\left(c\right), v\right)} = ite\left(b = c, 1, 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.cut_sector_gram` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The diagonal Gram entries are one and the off-diagonal entries are zero. Distinct prefix occupations have distinct complementary suffix occupations.

**Definition 1.12 (Maximum actual boundary size).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; boundaryMaximum\left(a\right) = FinsetSup\left(range\left(card\left(a\right) + 1\right), t \mapsto card\left(boundaries\left(a, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.boundaryMaximum` (`✓ std3`).

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The finite supremum ranges over every natural t in range(card(a)+1), including zero and the full cut. It is a maximum of actual cardinalities.

**Theorem 1.13 (Maximum Schmidt rank is the maximum actual boundary size).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; FinsetSup\left(range\left(card\left(a\right) + 1\right), t \mapsto rank\left(C\left(a, t, card\left(a\right) - t\right)\right)\right) = boundaryMaximum\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_max_schmidt_rank` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Every cut in the finite supremum satisfies t<=card(a), so the general rank theorem applies.

For the concrete statements, ast denotes occupation5040 on Option(Fin(3)), constructed as capacityOccupation(4,tailCapacities5040) with tail capacities (2,1,1). none is the count-four symbol; some(0), some(1), some(2) have counts two, one, one. rankAt(t) is rank(C(ast,t,8-t)), on actual words. r(t) denotes the landed timeSlice5040Count. The sequence below is transported from its existing theorem through the generic bounded-coordinate equivalence.

**Definition 1.14 (The actual occupation for 5040).**

$$ast = capacityOccupation\left(4, tailCapacities\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.occupation5040` (`✓ std3`).

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

tailCapacities is BoundedTimeSlice.tailCapacities5040 on Fin(3), namely (2,1,1).

**Theorem 1.15 (Eight actual time slots).**

$$card\left(ast\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.occupation_5040_card` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The generic capacity cardinality and landed tail sum give the actual multiset length.

**Theorem 1.16 (Actual history rank equals the landed slice count).**

$$\forall t \in \mathbb{N},\; t \le 8 \Rightarrow rank\left(C\left(ast, t, 8 - t\right)\right) = r\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_rank_eq_sliceCount` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The rank of the full coefficient matrix is its actual boundary count; the bounded-coordinate equivalence identifies that count with r(t).

**Theorem 1.17 (The nine actual cut ranks).**

$$map\left(t \mapsto rank\left(C\left(ast, t, 8 - t\right)\right), ListRange\left(9\right)\right) = List\left(1, 4, 8, 11, 12, 11, 8, 4, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_rank_sequence` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

ListRange(9) lists zero through eight. No independent rank or boundary enumeration is used.

**Theorem 1.18 (Every valid cut is bounded, with equality only at four).**

$$\forall t \in \mathbb{N},\; t \le 8 \Rightarrow \left(rank\left(C\left(ast, t, 8 - t\right)\right) \le 12 \land \left(rank\left(C\left(ast, t, 8 - t\right)\right) = 12 \Leftrightarrow t = 4\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_rank_bound` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

This consumes the landed unique maximum through the actual-rank transport.

**Theorem 1.19 (The actual maximum boundary size is twelve).**

$$boundaryMaximum\left(ast\right) = 12$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.occupation_5040_boundary_maximum` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The universal landed bound controls the supremum, and the actual cut four attains it.

**Theorem 1.20 (Maximum Schmidt rank twelve is attained at four).**

$$FinsetSup\left(range\left(9\right), t \mapsto rank\left(C\left(ast, t, 8 - t\right)\right)\right) = 12 \land rank\left(C\left(ast, 4, 4\right)\right) = 12$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_max_schmidt_rank` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

This is the maximum of the actual coefficient-matrix ranks of the eight-slot uniform occupation history, with an explicit attaining cut.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.boundaryMaximum`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_diagonal_restriction`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_eq_uniform_word`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_factorization`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.coefficient_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.cut_sector_gram`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_max_schmidt_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_rank_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_rank_eq_sliceCount`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_5040_rank_sequence`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.history_max_schmidt_rank`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.legal_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.normalized_coefficient_factorization`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.occupation5040`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.occupation_5040_boundary_maximum`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.occupation_5040_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_eq_sqrt_binomial`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_sq`
- Truth anchor: `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.schmidt_coefficient_sq_binomial`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](OccupancyWordSectors.md)
