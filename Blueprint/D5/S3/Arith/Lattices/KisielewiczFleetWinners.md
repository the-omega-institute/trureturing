# Nonperiodic cube fleets with infinitely many winner changes

## Abstract

Two fixed nonperiodic cube fleets have a non-eventually-periodic winner sequence.

A fleet consists of lattice origins whose translates of the discrete unit cube {0,1}³ cover each lattice point exactly once. The fleet has a trivial translation stabilizer if only the zero translation preserves the origin set. The base point is zero and the coordinate labels are fixed.

For any positive integral side a and shift e in {0,1}³, a score counts the fleet origins t with eᵢ ≤ tᵢ < eᵢ + a in each coordinate. The margin is the sum of signed score differences over the 64 equally likely ordered shift pairs. The outcome O is the sign of that margin.

**Theorem 1.1 (Two fixed fleets with no eventual outcome period).**

$$\exists F,G \subseteq \mathbb{Z}^{3}, \operatorname{UniqueCover}(F) \land \operatorname{UniqueCover}(G) \land \operatorname{TrivialStabilizer}(F) \land \operatorname{TrivialStabilizer}(G) \land (\forall B \in \mathbb{N}, \exists a,b \in \mathbb{N}, \max(1,B) \le a \land \max(1,B) \le b \land O_{F,G}(a) = 1 \land O_{F,G}(b) = -1) \land (\forall P \in \mathbb{N}, 0 < P \Rightarrow \forall B \in \mathbb{N}, \exists c \in \mathbb{N}, \max(1,B) \le c \land O_{F,G}(c + P) \neq O_{F,G}(c))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets` (`✓ std3`). ∎

*Resolves.* `Problems/kisielewicz-2026-nonperiodic-fleet-winners` (proved) by `D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kisielewicz-2026-nonperiodic-fleet-winners","declaration_gid":"D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrzej P. Kisielewicz (2026). *Local fluctuations, majorization, and nontransitivity in cube tilings of ℤᵈ*. DOI: [10.48550/arXiv.2611.09844](https://doi.org/10.48550/arXiv.2611.09844). URL: <https://arxiv.org/html/2611.09844v1#Thmproblem4.p3.1>.

*Commentary.*

Divide the vertical coordinate by two to choose a slab. In each ordinary slab the horizontal grid has one common parity. The exceptional row in slab −1 and exceptional column in slab −2 preserve unique cover and eliminate all nonzero translation periods.

At tₖ = 8ᵏ⁺¹(k+1)!, prescribe phase-zero totals 2tₖ and 3tₖ through slab 4tₖ+1 and swap them at alternate k. Each increment fits in its new block. The literal margin at side 8tₖ+3 is +4 or −4 according to that assignment. For every positive P, sufficiently late consecutive selected sides are both 3 modulo P. Their opposite outcomes force a change in some step of length P between them.

## References

- Truth anchor: `D5/S3/Arith/Lattices/KisielewiczFleetWinners.exists_nonperiodic_fleets`
