# The normalized cyclic analytic continuation

## Abstract

The normalized cyclic analytic continuation

The selected length r may be any natural number at most the order of chi; all selected positive powers are nonprincipal.

Use the entire normalized zeta factor and both Schwarz partners of each nontrivial character power. The zeta weight is one; each partner has half the original positive cyclic weight. The divided difference at one removes the artificial singularity before division by s.

**Theorem 1.1 (Agreement with the arithmetic transform).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicContinuation.continuation_half_plane_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicContinuation.continuation_half_plane_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized zeta logarithmic derivative and its value at one account exactly for the double-pole and linear corrections in the arithmetic transform.

**Theorem 1.2 (The actual simple poles).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicContinuation.continuation_actual_poles`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicContinuation.continuation_actual_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Its residue is minus the positive weighted sum of actual analytic orders, divided by the zero times the zero minus one. The positive weighted multiplicity cannot cancel. The continuation is analytic away from these locally discrete zeros and has the stated simple principal part at each zero.

**Theorem 1.3 (Every actual factor zero is left of one).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicContinuation.actualZeros_re_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicContinuation.actualZeros_re_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r at most the character order, every zero in the actual factor zero set has real part strictly less than one. The existing nonvanishing theorems apply to each factor and its Schwarz partner.

**Theorem 1.4 (Real actual zeros give positive real residues).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicContinuation.actual_real_residue_pos`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicContinuation.actual_real_residue_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an actual zero z with zero imaginary part, the residue has positive real part and zero imaginary part. The zero lies between zero and one, so minus one divided by z(z-1) is positive; its weighted analytic multiplicity is positive as well.

**Theorem 1.5 (Ordinary zeta zeros occur in the actual factor set).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicContinuation.zeta_zero_mem_actualZeros`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicContinuation.zeta_zero_mem_actualZeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every zero of ordinary zeta with positive real part belongs to the actual zero set. Nonvanishing of the totalized zeta value at one supplies z different from one inside the proof.

**Theorem 1.6 (Cyclic-power zeros occur in the actual factor set).**

Lean statement: `D5/S3/CharacterSums/DirichletCyclicContinuation.member_zero_mem_actualZeros`

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletCyclicContinuation.member_zero_mem_actualZeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index j in Fin(r-1), a zero of the L-function of chi to the power j+1 with positive real part belongs to the actual zero set.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicContinuation.actualZeros_re_lt_one`
- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicContinuation.actual_real_residue_pos`
- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicContinuation.continuation_actual_poles`
- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicContinuation.continuation_half_plane_laplace`
- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicContinuation.member_zero_mem_actualZeros`
- Truth anchor: `D5/S3/CharacterSums/DirichletCyclicContinuation.zeta_zero_mem_actualZeros`
- Dependency: [D5/S3/Analytic/Isolation/VerticalNearestPole](../Analytic/Isolation/VerticalNearestPole.md)
- Dependency: [D5/S3/CharacterSums/DirichletCyclicLaplace](DirichletCyclicLaplace.md)
