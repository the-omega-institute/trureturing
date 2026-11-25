# Nonperiodic cube fleets with infinitely many winner changes

## Abstract

Two fixed nonperiodic cube fleets have a non-eventually-periodic winner sequence.

The base point is zero and the coordinate labels are fixed.

**Definition 1.1 (Lattice origins).**

$$\operatorname{Origin} = \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.Origin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An origin specifies the three integer coordinates of a cube.

**Definition 1.2 (Window shifts).**

$$\operatorname{Shift} = \operatorname{Bool} \times \operatorname{Bool} \times \operatorname{Bool}$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.Shift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate shifts the base point by zero or one.

**Definition 1.3 (Shift coordinate).**

$$\operatorname{bit}(\operatorname{false}) = 0,\quad\operatorname{bit}(\operatorname{true}) = 1$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.bit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean coordinates are interpreted as integers.

**Definition 1.4 (One coordinate of the window).**

$$\operatorname{axis}(a, s) = \{x \in \mathbb{Z} \mid \operatorname{bit}(s) \le x < \operatorname{bit}(s) + (a : \mathbb{Z})\}$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.axis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer interval contains its lower endpoint and excludes its upper endpoint.

**Definition 1.5 (Window of origins).**

$$\operatorname{box}(a, (s_{1}, s_{2}, s_{3})) = \operatorname{axis}(a, s_{1}) \times \operatorname{axis}(a, s_{2}) \times \operatorname{axis}(a, s_{3})$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.box` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three intervals use the same natural side and the corresponding shift coordinates.

**Definition 1.6 (Number of fleet origins in the window).**

$$\operatorname{score}(F, a, s) = \operatorname{card}(\{t \in \operatorname{box}(a, s) \mid t \in F\})$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.score` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The score is the cardinality of the fleet origins in the shifted window.

**Definition 1.7 (Signed comparison of two fleets).**

$$\operatorname{margin}(F, G, a) = \sum_{(e, s) \in \operatorname{Shift} \times \operatorname{Shift}} \operatorname{sign}((\operatorname{score}(F, a, e) : \mathbb{Z}) - (\operatorname{score}(G, a, s) : \mathbb{Z}))$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.margin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All 64 ordered shift pairs are equally likely. Each pair contributes one, zero, or minus one according to the comparison of the two integer-valued counts.

**Definition 1.8 (Strict winner).**

$$\operatorname{outcome}(F, G, a) = \operatorname{sign}(\operatorname{margin}(F, G, a))$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.outcome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign gives one for a strict win by the first fleet, minus one for a strict win by the second fleet, and zero when the win probabilities are equal.

**Definition 1.9 (Membership in a translated discrete cube).**

$$\operatorname{Covers}(t, p) \iff (\forall i \in \{1,2,3\}, t_{i} \le p_{i} < t_{i} + 2)$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.Covers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate of the point differs from the origin by zero or one.

**Definition 1.10 (Unique lattice cover).**

$$\operatorname{UniqueCover}(F) \iff (\forall p \in \operatorname{Origin}, \exists! t \in F, \operatorname{Covers}(t, p))$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.UniqueCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every lattice point belongs to the cube of exactly one fleet origin.

**Definition 1.11 (Trivial translation stabilizer).**

$$\operatorname{TrivialStabilizer}(F) \iff (\forall d \in \operatorname{Origin}, (\forall t \in \operatorname{Origin}, t + d \in F \iff t \in F) \Rightarrow d = (0,0,0))$$

*Formalization.* `D5/S3/Arith/Lattices/KisielewiczFleetWinners.TrivialStabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A translation preserves the fleet when it preserves origin membership.

**Theorem 1.12 (Two fixed fleets with no eventual outcome period).**

$$\exists F,G \subseteq \mathbb{Z}^{3}, \operatorname{UniqueCover}(F) \land \operatorname{UniqueCover}(G) \land \operatorname{TrivialStabilizer}(F) \land \operatorname{TrivialStabilizer}(G) \land (\forall B \in \mathbb{N}, \exists a,b \in \mathbb{N}, \max(1,B) \le a \land \max(1,B) \le b \land \operatorname{outcome}(F, G, a) = 1 \land \operatorname{outcome}(F, G, b) = -1) \land (\forall P \in \mathbb{N}, 0 < P \Rightarrow \forall B \in \mathbb{N}, \exists c \in \mathbb{N}, \max(1,B) \le c \land \operatorname{outcome}(F, G, c + P) \neq \operatorname{outcome}(F, G, c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets` (`✓ std3`). ∎

*Resolves.* `Problems/kisielewicz-2026-nonperiodic-fleet-winners` (proved) by `D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kisielewicz-2026-nonperiodic-fleet-winners","declaration_gid":"D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrzej P. Kisielewicz (2026). *Local fluctuations, majorization, and nontransitivity in cube tilings of ℤᵈ*. DOI: [10.48550/arXiv.2611.09844](https://doi.org/10.48550/arXiv.2611.09844). URL: <https://arxiv.org/html/2611.09844v1#Thmproblem4.p3.1>.

*Commentary.*

Divide the vertical coordinate by two to choose a slab. In each ordinary slab the horizontal grid has one common parity. The exceptional row in slab −1 and exceptional column in slab −2 preserve unique cover and eliminate all nonzero translation periods.

At tₖ = 8ᵏ⁺¹(k+1)!, prescribe phase-zero totals 2tₖ and 3tₖ through slab 4tₖ+1 and swap them at alternate k. Each increment fits in its new block. The literal margin at side 8tₖ+3 is +4 or −4 according to that assignment. For every positive P, sufficiently late consecutive selected sides are both 3 modulo P. Their opposite outcomes force a change in some step of length P between them.

## References

- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.Covers`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.Origin`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.Shift`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.TrivialStabilizer`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.UniqueCover`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.axis`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.bit`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.box`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.margin`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.outcome`
- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.score`
