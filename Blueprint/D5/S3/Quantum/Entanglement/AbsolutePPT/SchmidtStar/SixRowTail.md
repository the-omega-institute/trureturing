# SixRowTail

## Abstract

At every nonnegative unit five-vector, six distinct labelled K6 bottom slots have coefficient mass at least three. A six-cycle and the fifteen complementary labels give a total assignment of all twenty-one capped deficits with charge at least half their squared mass.

This is the constructive tail supplier at the same p used by SixRowHead.head_exists. Put z = (1,p). A diagonal slot has coefficient z_i squared and an edge slot has coefficient z_i z_j. Only the five coordinate labels are sorted by minus p; the head p and its edge labelling are retained literally. No coefficient ordering or optimizer is used.

If the sum of p is at least two, select the centre diagonal and all five centre edges. Otherwise write the sorted coordinate values as alpha, beta, gamma, delta, epsilon. Their squared sum is one and their sum is at most two. The inequalities one <= alpha times the coordinate sum and one <= alpha squared + beta times the remaining coordinate sum imply alpha + beta >= one. Bounding delta squared + epsilon squared by gamma times delta + epsilon then yields alpha + beta + gamma + alpha squared + beta squared >= two. Select the centre diagonal, the first three centre edges, and the first two successor diagonals. The six labels remain distinct even at ties and zeros.

Reverse the increasing twenty-one deficits. With t the sixth reversed entry and T the sum of the first six, every first-block square is at most x + t x - t, and every other square is at most t x. Summing all twenty-one inequalities gives q <= T + t(D - 6) <= T. Enumerate the six selected slots and their fifteen-slot complement. The six cyclic selected-block charges sum to T times the selected coefficient mass, at least 3T; one cycle has charge at least T/2. Complete this cycle with every complementary label, then reverse the resulting twenty-one indices. The selected image is exactly 15 through 20 and the complement image is 0 through 14.

The assignment covers all twenty-one bottom labels and charges the deficits at the original head vector. The selected six labels and their complement remain disjoint even when coefficients tie.

**Definition 1.1 (coefficient).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.coefficient`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def coefficient (p : Fin 5 → ℝ) : BottomSlot 6 → ℝ := Sum.elim (fun i => (Fin.cases 1 p i)^2) (fun e => (Fin.cases 1 p e.val.1)*(Fin.cases 1 p e.val.2))

**Definition 1.2 (tail charge).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tailCharge`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tailCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def tailCharge (d : Fin 21 → ℝ) (p : Fin 5 → ℝ) (σ : BottomSlot 6 ≃ Fin 21) : ℝ := ∑ B, d (σ B)*coefficient p B

**Theorem 1.3 (six coefficient mass).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.six_coefficient_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.six_coefficient_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem six_coefficient_mass (p : Fin 5 → ℝ) (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, (p i)^2=1) : ∃ S : Finset (BottomSlot 6), S.card=6 ∧ 3 ≤ ∑ B ∈ S, coefficient p B

**Theorem 1.4 (all twenty-one capped squares).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.capped_tail_squares`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.capped_tail_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem capped_tail_squares (x : Fin 21 → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (ho : Antitone x) (hm : ∑ i, x i ≤ 6) : (∑ i, (x i)^2) ≤ ∑ i, if i.val < 6 then x i else 0

**Theorem 1.5 (total same-vector tail assignment).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tail_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tail_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem tail_exists (d : Fin 21 → ℝ) (p : Fin 5 → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (hdo : Monotone d) (hm : ∑ i, d i ≤ 6) (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, (p i)^2=1) : ∃ σ : BottomSlot 6 ≃ Fin 21, (∑ i, (d i)^2)/2 ≤ tailCharge d p σ

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.capped_tail_squares`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.coefficient`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.six_coefficient_mass`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tailCharge`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tail_exists`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead](SixRowHead.md)
