# Guarded moves and projector charge on the periodic ladder

## Abstract

The guarded matrix entries determine charge conservation and two-sided annihilation.

Labelled words of length L use the empty rung and the symmetric and antisymmetric one-boson rungs of Eq. (69). Config is the subtype in which each cyclic consecutive pair has an empty rung. All scalar actions use the complex numbers. A matrix entry has the output word as its row and the input word as its column.

The diagonal entry of P at site j is the indicator of a minus at j plus the squared difference of the two flanking empty indicators. The unextended charge adds these indicators over the cycle as in Eq. (45). The centre move A interchanges empty and plus at j with both flanks empty. The flank move F interchanges both occupied signs about an empty centre. Both moves use unit matrix entries. Their sum is the unextended generator S of Eq. (70). The controlled generator T is C times S, where C is the square of the difference of the two flanking projectors.

Jammed means that at every site with projector value zero, the two flanking projector values agree. The diagonal control then kills the row of a jammed word at that site. A site of projector value one has no move. The guarded involutions complement the flanking projector bits for each move, so the same condition kills the column as well. A nonzero controlled move must exchange the two flanking bits and preserve every other projector bit.

**Theorem 1.1 (Periodic successor index).**

$$\forall (L: \mathbb{N}), \forall (j: \operatorname{Fin}\left(L\right)), \operatorname{val}\left(\operatorname{next}\left(j\right)\right) = \operatorname{if}\left(\operatorname{val}\left(j\right) + 1 < L, \operatorname{val}\left(j\right) + 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.next_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The successor of the last rung is the first rung.

**Theorem 1.2 (Periodic predecessor index).**

$$\forall (L: \mathbb{N}), \forall (j: \operatorname{Fin}\left(L\right)), \operatorname{val}\left(\operatorname{prev}\left(j\right)\right) = \operatorname{if}\left(\operatorname{val}\left(j\right) = 0, L-1, \operatorname{val}\left(j\right)-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.prev_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The predecessor of the first rung is the last rung.

**Theorem 1.3 (Two-sided annihilation by the local generator).**

$$\forall (L: \mathbb{N}), 5 \le L \Rightarrow \forall (j: \operatorname{Fin}\left(L\right)), \forall (x: \operatorname{Config}\left(L\right)), \operatorname{Jammed}\left(x\right) \Rightarrow \left(\operatorname{mulVec}\left(\operatorname{T}\left(j\right), \operatorname{ket}\left(x\right)\right) = 0 \land \operatorname{vecMul}\left(\operatorname{ket}\left(x\right), \operatorname{T}\left(j\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.jammed_kills` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The delta vector is the basis ket and the same coordinates give its dual row.

**Theorem 1.4 (Charge across a nonzero entry).**

$$\forall (L: \mathbb{N}), 5 \le L \Rightarrow \forall (j: \operatorname{Fin}\left(L\right)), \forall (x: \operatorname{Config}\left(L\right)), \forall (y: \operatorname{Config}\left(L\right)), \operatorname{entry}\left(\operatorname{T}\left(j\right), y, x\right) \ne 0 \Rightarrow \operatorname{charge}\left(y\right) = \operatorname{charge}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.charge_of_nonzero_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The two complemented bits have sum one on each endpoint of a controlled move.

**Theorem 1.5 (Projector charge of a basis ket).**

$$\forall (L: \mathbb{N}), \forall (x: \operatorname{Config}\left(L\right)), \operatorname{mulVec}\left(\operatorname{NP}\left(L\right), \operatorname{ket}\left(x\right)\right) = \operatorname{smul}\left(\operatorname{ofNat}\left(\operatorname{charge}\left(x\right)\right), \operatorname{ket}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.charge_eigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The diagonal matrix of summed charge acts by the complex cast of that charge.

**Theorem 1.6 (Square of the controlled generator).**

$$\forall (L: \mathbb{N}), 5 \le L \Rightarrow \forall (j: \operatorname{Fin}\left(L\right)), \operatorname{T}\left(j\right)^{2} = \operatorname{C}\left(j\right) \cdot \operatorname{S}\left(j\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.controlled_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The control is idempotent and constant across each transition of the unextended move.

**Theorem 1.7 (The two contributions to each ladder density).**

$$\forall (L: \mathbb{N}), 5 \le L \Rightarrow \forall (j: \operatorname{Fin}\left(L\right)), \operatorname{T}\left(j\right) = \operatorname{Ue}\left(j\right) \cdot \operatorname{A}\left(j\right) + \operatorname{Um}\left(j\right) \cdot \operatorname{F}\left(j\right) \land \operatorname{T}\left(j\right)^{2} = \operatorname{Ue}\left(j\right) \cdot \operatorname{DA}\left(j\right) + \operatorname{Um}\left(j\right) \cdot \operatorname{DF}\left(j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.ladder_density_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

Ue is the squared difference of the two empty projectors at distance two. Um is the squared difference of the minus projectors on the adjacent sites. DA is the projector onto a centre that is not minus with two empty flanks. DF projects onto two occupied flanks. These give the two five-rung pieces in Eq. (71).

**Theorem 1.8 (Each controlled ladder contribution annihilates a jammed word).**

$$\forall (L: \mathbb{N}), 5 \le L \Rightarrow \forall (x: \operatorname{Config}\left(L\right)), \operatorname{Jammed}\left(x\right) \Rightarrow \forall (j: \operatorname{Fin}\left(L\right)), \left(\operatorname{mulVec}\left(\operatorname{Ue}\left(j\right) \cdot \operatorname{A}\left(j\right), \operatorname{ket}\left(x\right)\right) = 0 \land \operatorname{vecMul}\left(\operatorname{ket}\left(x\right), \operatorname{Ue}\left(j\right) \cdot \operatorname{A}\left(j\right)\right) = 0\right) \land \left(\left(\operatorname{mulVec}\left(\operatorname{Um}\left(j\right) \cdot \operatorname{F}\left(j\right), \operatorname{ket}\left(x\right)\right) = 0 \land \operatorname{vecMul}\left(\operatorname{ket}\left(x\right), \operatorname{Um}\left(j\right) \cdot \operatorname{F}\left(j\right)\right) = 0\right) \land \left(\left(\operatorname{mulVec}\left(\operatorname{Ue}\left(j\right) \cdot \operatorname{DA}\left(j\right), \operatorname{ket}\left(x\right)\right) = 0 \land \operatorname{vecMul}\left(\operatorname{ket}\left(x\right), \operatorname{Ue}\left(j\right) \cdot \operatorname{DA}\left(j\right)\right) = 0\right) \land \left(\operatorname{mulVec}\left(\operatorname{Um}\left(j\right) \cdot \operatorname{DF}\left(j\right), \operatorname{ket}\left(x\right)\right) = 0 \land \operatorname{vecMul}\left(\operatorname{ket}\left(x\right), \operatorname{Um}\left(j\right) \cdot \operatorname{DF}\left(j\right)\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.ladder_parts_kill` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuan Miao, Kohei Fukai (2026). *A Novel Algebraic Approach to Medium-Range Solvable Models*. URL: <https://arxiv.org/pdf/2611.29351v1>.

*Commentary.*

The centre and flank contributions have disjoint support for both the first and second powers, giving separate row and column vanishing.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.charge_eigenvalue`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.charge_of_nonzero_entry`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.controlled_square`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.jammed_kills`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.ladder_density_parts`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.ladder_parts_kill`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.next_val`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.prev_val`
