# A counterexample to the printed CRIM formula

## Abstract

The CRIM Grundy value of (6,6,5,4,3,2,1) is 1, contradicting the printed prediction 3.

**Definition 1.1 (Deleting rows and columns).**

Lean statement: `D5/S0/Certificates/Games/CrimGrundyRefutation.moves`

*Formalization.* `D5/S0/Certificates/Games/CrimGrundyRefutation.moves` (`✓ std3`).

*Citation.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

A position is a decreasing list of positive row lengths. A move removes one row, or conjugates the partition, removes one row, and conjugates back. Conjugation counts the rows reaching each column and omits zero heights. The empty partition has no options. These are the moves of section 3, including the reattachment of the remaining parts.

**Definition 1.2 (The recursive Grundy value).**

Lean statement: `D5/S0/Certificates/Games/CrimGrundyRefutation.grundy`

*Formalization.* `D5/S0/Certificates/Games/CrimGrundyRefutation.grundy` (`✓ std3`).

*Citation.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

The Grundy value is the least natural number absent from the values of all options. Mathlib finite minima define this least excluded number. Conjugation preserves the total number of cells and every move strictly decreases it, so recursion on cell count defines the value from terminal positions.

**Lemma 1.3 (Removing zero rows preserves the cell count).**

$$\forall p \in \operatorname{Position},\; \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{filter}\left((\lambda (n:\mathbb{N})\mapsto\operatorname{bne}\left(n, 0\right)), p\right)\right) = \operatorname{List}.\operatorname{sum}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/CrimGrundyRefutation.sum_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

Filtering zero entries from a list of natural row lengths preserves its sum.

**Lemma 1.4 (Every move removes cells).**

$$\forall p \in \operatorname{Position},\; \forall q \in \operatorname{Position},\; (q \in \operatorname{moves}\left(p\right)) \Rightarrow (\operatorname{List}.\operatorname{sum}\left(q\right) < \operatorname{List}.\operatorname{sum}\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/CrimGrundyRefutation.move_decreases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

For arbitrary natural lists, every CRIM follower has strictly smaller total cell count.

**Lemma 1.5 (The mex equation).**

$$\forall p \in \operatorname{Position},\; \operatorname{grundy}\left(p\right) = \operatorname{mex}\left(\operatorname{List}.\operatorname{toFinset}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{grundy}, \operatorname{moves}\left(p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/CrimGrundyRefutation.grundy_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

The well-founded evaluator equals the least natural number absent from the Grundy values of all legal followers.

**Definition 1.6 (Conjecture 3 as printed).**

Lean statement: `D5/S0/Certificates/Games/CrimGrundyRefutation.claim`

*Formalization.* `D5/S0/Certificates/Games/CrimGrundyRefutation.claim` (`✓ std3`).

*Citation.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

For positive r,c and 0 ≤ k < min(r,c), the rectair R^k_{r,c} has r-k copies of c followed by c-1 through c-k. For r ≥ 7, printed Conjecture 3 predicts that R^k_{r,r-1} has Grundy value 3 when k=r-2 and r is odd, and value 1 otherwise. The claim uses precisely these valid parameters and the CRIM recursion.

**Theorem 1.7 (The value at r=7 and k=5).**

Lean statement: `D5/S0/Certificates/Games/CrimGrundyRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/CrimGrundyRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ina Bašić; Eric Gottlieb; Matjaž Krnc (2026). *CRIM: A Natural Game on Integer Partitions*. DOI: [10.48550/arXiv.2606.16828](https://doi.org/10.48550/arXiv.2606.16828). URL: <https://arxiv.org/abs/2606.16828v1>.

*Commentary.*

The partition R^5_{7,6} is (6,6,5,4,3,2,1). A finite certificate contains every descendant, starting with the empty partition. At every position the kernel checks that all options are present, the assigned value is absent from their values, and every smaller natural number occurs. Induction on cell count identifies the certificate values with the recursive Grundy values.

The twelve distinct options have value set {0,2,4,5}. Its least excluded value is 1. Since 7 is odd and 5=7-2, the displayed formula instead predicts 3. The theorem negates only the r ≥ 7 formula of printed Conjecture 3. No priority, conclusion about other results, or corrected formula is asserted.

## References

- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.grundy`
- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.grundy_eq`
- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.move_decreases`
- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.moves`
- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.result`
- Truth anchor: `D5/S0/Certificates/Games/CrimGrundyRefutation.sum_nonzero`
