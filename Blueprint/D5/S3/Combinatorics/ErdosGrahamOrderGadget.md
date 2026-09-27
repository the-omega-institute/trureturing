# The Erdos-Graham Order Gadget Is Impossible at Every Scale

## Abstract

Every order gadget on the integers from M plus one through twice M fails once M is at least sixteen: arithmetic-progression constraints propagate two neighbouring centres around ladders whose guard endpoints force both possible rank orders.

**Definition 1.1 (The dyadic block).**

$$\forall M \in \mathbb{N},\; \operatorname{block}\left(M\right) = \{n \in \mathbb{N} | M + 1 \le n \le 2 \cdot M\}$$

*Formalization.* `D5/S3/Combinatorics/ErdosGrahamOrderGadget.block` (`✓ std3`).

*Citation.* William Kasel (2026). *Structural rigidity in the Erdős–Graham two-set permutation problem*. URL: <https://arxiv.org/abs/2609.02939v1>.

*Commentary.*

For each natural M, the block consists of exactly the natural numbers from M plus one through twice M, with both endpoints included.

**Definition 1.2 (No monotone three-term progression).**

$$\forall M \in \mathbb{N}, rank \in \mathbb{N} \to \mathbb{N},\; (\operatorname{APFree}\left(M, rank\right)) \Leftrightarrow (\forall a \in \mathbb{N}, b \in \mathbb{N}, c \in \mathbb{N},\; ((a \in \operatorname{block}\left(M\right)) \land \left((b \in \operatorname{block}\left(M\right)) \land \left((c \in \operatorname{block}\left(M\right)) \land \left((a < b) \land \left((b < c) \land (a + c = 2 \cdot b)\right)\right)\right)\right)) \Rightarrow ((\neg (\operatorname{rank}\left(a\right) < \operatorname{rank}\left(b\right) < \operatorname{rank}\left(c\right))) \land (\neg (\operatorname{rank}\left(c\right) < \operatorname{rank}\left(b\right) < \operatorname{rank}\left(a\right)))))$$

*Formalization.* `D5/S3/Combinatorics/ErdosGrahamOrderGadget.APFree` (`✓ std3`).

*Citation.* William Kasel (2026). *Structural rigidity in the Erdős–Graham two-set permutation problem*. URL: <https://arxiv.org/abs/2609.02939v1>.

*Commentary.*

A ranking is progression-free when no increasing three-term arithmetic progression inside the block has ranks increasing from left to right or increasing from right to left.

**Definition 1.3 (The guard inequalities).**

$$\forall M \in \mathbb{N}, rank \in \mathbb{N} \to \mathbb{N},\; (\operatorname{Guards}\left(M, rank\right)) \Leftrightarrow (\forall x \in \left\{15, 16\right\},\; \forall j \in \mathbb{N},\; ((1 \le j) \land (j \le \left\lfloor\frac{x}{2}\right\rfloor)) \Rightarrow (\operatorname{rank}\left(2 \cdot M + 2 \cdot j - x\right) < \operatorname{rank}\left(M + j\right)))$$

*Formalization.* `D5/S3/Combinatorics/ErdosGrahamOrderGadget.Guards` (`✓ std3`).

*Citation.* William Kasel (2026). *Structural rigidity in the Erdős–Graham two-set permutation problem*. URL: <https://arxiv.org/abs/2609.02939v1>.

*Commentary.*

For each of fifteen and sixteen, every index from one through half that value places the corresponding top, twice M plus twice the index minus the value, before the bottom M plus the index.

**Definition 1.4 (Feasibility of the order gadget).**

$$\forall M \in \mathbb{N},\; (\operatorname{OrderGadget}\left(M\right)) \Leftrightarrow (\exists rank \in \mathbb{N} \to \mathbb{N},\; (\forall a \in \operatorname{block}\left(M\right), b \in \operatorname{block}\left(M\right),\; (\operatorname{rank}\left(a\right) = \operatorname{rank}\left(b\right)) \Rightarrow (a = b)) \land \left((\operatorname{APFree}\left(M, rank\right)) \land (\operatorname{Guards}\left(M, rank\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/ErdosGrahamOrderGadget.OrderGadget` (`✓ std3`).

*Citation.* William Kasel (2026). *Structural rigidity in the Erdős–Graham two-set permutation problem*. URL: <https://arxiv.org/abs/2609.02939v1>.

*Commentary.*

An order gadget at scale M is a natural-valued ranking that is injective on the block and obeys both the progression-free condition and all guard inequalities.

**Definition 1.5 (Impossibility from scale sixteen).**

$$(claim) \Leftrightarrow (\forall M \in \mathbb{N},\; (16 \le M) \Rightarrow (\neg \operatorname{OrderGadget}\left(M\right)))$$

*Formalization.* `D5/S3/Combinatorics/ErdosGrahamOrderGadget.claim` (`✓ std3`).

*Citation.* William Kasel (2026). *Structural rigidity in the Erdős–Graham two-set permutation problem*. URL: <https://arxiv.org/abs/2609.02939v1>.

*Commentary.*

The assertion says that no order gadget exists for any natural scale M at least sixteen.

**Theorem 1.6 (The order gadget is impossible).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosGrahamOrderGadget.result` (`✓ std3`). ∎

*Resolves.* `Problems/erdos-197-order-gadget-all-residues` (proved) by `D5/S3/Combinatorics/ErdosGrahamOrderGadget.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erdos-197-order-gadget-all-residues","declaration_gid":"D5/S3/Combinatorics/ErdosGrahamOrderGadget.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* William Kasel (2026). *Structural rigidity in the Erdős–Graham two-set permutation problem*. URL: <https://arxiv.org/abs/2609.02939v1>.

*Commentary.*

Split once on the rank order of two adjacent block elements; this determines which parity leads on the difference-one ladder. In each branch choose two centres c and c plus two just below three M over two. Two floods on the relevant parity class carry c and c plus two before a guard top, and the guards carry them before the corresponding bottoms. Two further floods on classes modulo four then give c before c plus two and c plus two before c. For even M the four guards are (15,2), (15,4), (16,1), and (16,3); for odd M they are (15,1), (15,3), (16,2), and (16,4). The phase-independent flood applies to even as well as odd classes modulo four, so both initial rank orders end in the same contradiction.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosGrahamOrderGadget.APFree`
- Truth anchor: `D5/S3/Combinatorics/ErdosGrahamOrderGadget.Guards`
- Truth anchor: `D5/S3/Combinatorics/ErdosGrahamOrderGadget.OrderGadget`
- Truth anchor: `D5/S3/Combinatorics/ErdosGrahamOrderGadget.block`
- Truth anchor: `D5/S3/Combinatorics/ErdosGrahamOrderGadget.claim`
- Truth anchor: `D5/S3/Combinatorics/ErdosGrahamOrderGadget.result`
