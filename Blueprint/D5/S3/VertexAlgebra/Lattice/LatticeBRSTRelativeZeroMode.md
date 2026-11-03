# Original relative BRST zero modes and literal shell stability

## Abstract

Original relative BRST zero modes and literal shell stability

All states belong to the original all-charge lattice matter tensor ghost carrier. The lattice has arbitrary integral symmetric even Gram matrix and arbitrary natural rank, including zero. All mode sums range over the integers and are finite only after application to each state. There is no hidden finite cutoff, vacuum change or intercept shift. H is arbitrary unless both H*gramComplex D=1 and gramComplex D*H=1 are explicitly displayed.

The existing native LatticeRelativeMassShell.totalCharge_mem_fixedMomentum and totalCharge_mem_relativeMassShell already prove preservation by the original Q. Together with equality of Qhat and Q on the literal relative domain, these laws give its momentum component. The finite row/column/diagonal decomposition identifies the zero-mode-free action needed for a later HPL bridge.

**Definition 1.1 (State).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.State`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unchanged carrier is the original lattice matter Carrier D tensored with the original algebraic ghost occupation Fock space.

Exact source telescope: abbrev State (D : LatticeData)

**Definition 1.2 (L0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.L0`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.L0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the actual unshifted matterMode D H 0 plus ghostVirasoro D 0.

Exact source telescope: abbrev L0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D)

**Definition 1.3 (cubicZeroFree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cubicZeroFree`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cubicZeroFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original cubicTerm is summed after application to v. The integer pair survives exactly when p, q and p+q are nonzero. Local finite support proves linearity; no endomorphism-valued infinite sum is used.

Exact source telescope: def cubicZeroFree : Module.End ℂ Fock

**Definition 1.4 (matterZeroFree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.matterZeroFree`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.matterZeroFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original finite-on-each-state matter summation has only its m=0 summand removed. Negative modes and zero lattice charge remain in scope.

Exact source telescope: def matterZeroFree (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D)

**Definition 1.5 (ghostZeroFree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostZeroFree`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostZeroFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is identity on the unchanged matter carrier tensored with cubicZeroFree.

Exact source telescope: def ghostZeroFree (D : LatticeData) : Module.End ℂ (State D)

**Definition 1.6 (zeroModeFreeCharge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.zeroModeFreeCharge`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.zeroModeFreeCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite matter tail plus the lifted finite cubic tail, with the original coefficients and normal ordering.

Exact source telescope: def zeroModeFreeCharge (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D)

**Theorem 1.7 (ghost_b_zero_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_b_zero_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_b_zero_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual zero b mode squares to zero by the original all-integer CAR, transported through the tensor lift. It gives the b projection and the Qhat anticommutator.

Exact source telescope: theorem ghost_b_zero_square (D : LatticeData) : ghostB D 0 * ghostB D 0 = 0

**Theorem 1.8 (ghost_c_zero_square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_c_zero_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_c_zero_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual zero c mode squares to zero by the original CAR. It shows that the c projection maps into ker c0.

Exact source telescope: theorem ghost_c_zero_square (D : LatticeData) : ghostC D 0 * ghostC D 0 = 0

**Theorem 1.9 (ghost_zero_mixed).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_zero_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_zero_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original tensor b0 and c0 have anticommutator identity. This gives both kernel-fixing laws and the direct decomposition.

Exact source telescope: theorem ghost_zero_mixed (D : LatticeData) : ghostB D 0 * ghostC D 0 + ghostC D 0 * ghostB D 0 = (1 : Module.End ℂ (State D))

**Definition 1.10 (bZeroProjector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual ordered product b0*c0; it is a projection onto ker b0, not an assumed projector.

Exact source telescope: def bZeroProjector (D : LatticeData) : Module.End ℂ (State D)

**Definition 1.11 (cZeroProjector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual ordered product c0*b0; it is a projection onto ker c0.

Exact source telescope: def cZeroProjector (D : LatticeData) : Module.End ℂ (State D)

**Theorem 1.12 (ghostB_bZeroProjector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostB_bZeroProjector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostB_bZeroProjector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The b0 image of the literal b0*c0 product vanishes. Thus the product maps into the stated kernel.

Exact source telescope: theorem ghostB_bZeroProjector (D : LatticeData) : ghostB D 0 * bZeroProjector D = 0

**Theorem 1.13 (ghostC_cZeroProjector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostC_cZeroProjector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostC_cZeroProjector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The c0 image of the literal c0*b0 product vanishes. Thus the product maps into the stated kernel.

Exact source telescope: theorem ghostC_cZeroProjector (D : LatticeData) : ghostC D 0 * cZeroProjector D = 0

**Theorem 1.14 (bZeroProjector_fix_of_ker).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector_fix_of_ker`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector_fix_of_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal b0*c0 product fixes every vector annihilated by b0. This is the kernel-fixing field of the native projection.

Exact source telescope: theorem bZeroProjector_fix_of_ker (D : LatticeData) (x : State D) (hx : ghostB D 0 x = 0) : bZeroProjector D x = x

**Theorem 1.15 (cZeroProjector_fix_of_ker).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector_fix_of_ker`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector_fix_of_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal c0*b0 product fixes every vector annihilated by c0.

Exact source telescope: theorem cZeroProjector_fix_of_ker (D : LatticeData) (x : State D) (hx : ghostC D 0 x = 0) : cZeroProjector D x = x

**Theorem 1.16 (bZeroProjector_isProj).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector_isProj`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector_isProj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual product maps every state into ker b0 and fixes that kernel. Mathlib LinearMap.IsProj.isIdempotentElem supplies its idempotence directly, without another wrapper theorem. Its codomain restriction is one coordinate of the direct decomposition.

Exact source telescope: theorem bZeroProjector_isProj (D : LatticeData) : LinearMap.IsProj (LinearMap.ker (ghostB D 0)) (bZeroProjector D)

**Theorem 1.17 (cZeroProjector_isProj).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector_isProj`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector_isProj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual product maps every state into ker c0 and fixes that kernel; its idempotence follows from the same native projection interface. Its codomain restriction is the other coordinate of the direct decomposition.

Exact source telescope: theorem cZeroProjector_isProj (D : LatticeData) : LinearMap.IsProj (LinearMap.ker (ghostC D 0)) (cZeroProjector D)

**Definition 1.18 (zeroModeDecomposition).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.zeroModeDecomposition`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.zeroModeDecomposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A linear equivalence sends x to (b0*c0*x,c0*b0*x) in ker b0 times ker c0; its inverse adds the two original states. The original CAR proves both inverse laws. This is a native splitting of the original space, not a replacement carrier.

Exact source telescope: def zeroModeDecomposition (D : LatticeData) : State D ≃ₗ[ℂ] (LinearMap.ker (ghostB D 0) × LinearMap.ker (ghostC D 0))

**Theorem 1.19 (totalL0_b_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.totalL0_b_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.totalL0_b_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original total zero mode commutes with b0 for arbitrary H. The matter and ghost factors commute separately; ghost Ward at (0,0) has zero coefficient.

Exact source telescope: theorem totalL0_b_zero (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : L0 D H * ghostB D 0 - ghostB D 0 * L0 D H = 0

**Definition 1.20 (Qhat).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly totalCharge D H minus c0*L0 minus b0*R0, using the original totalCharge=T+id tensor Qg and the original R0. This definition does not postulate decomposition or stability.

Exact source telescope: def Qhat (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D)

**Theorem 1.21 (Qhat_b_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_b_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_b_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual b0 anticommutator of Qhat vanishes. The total b Ward law, zero CAR and the ordinary even R0-b0 commutator prove cancellation.

Exact source telescope: theorem Qhat_b_zero (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Qhat D H * ghostB D 0 + ghostB D 0 * Qhat D H = 0

**Theorem 1.22 (ghost_zero_split).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_zero_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_zero_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original statewise finite ordered-pair cubic sum splits into c0*Lg0 plus b0*R0 plus the zero-free tail. The proof partitions the zero row and column with their zero overlap, the remaining p+q=0 diagonal, and the tail. Both normal-order branches and every integer pair remain included.

Exact source telescope: theorem ghost_zero_split (v : Fock) : BcGhostBRST.Qg v = c 0 (BcGhostVirasoro.L 0 v) + b 0 (BcGhostBRST.R 0 v) + cubicZeroFree v

**Theorem 1.23 (matter_zero_split).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.matter_zero_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.matter_zero_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual m=0 matter summand is matterMode D H 0 times c0. Its complement is the original matterZeroFree sum; no inverse-Gram condition is required.

Exact source telescope: theorem matter_zero_split (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) : T D H x = (matterMode D H 0 * ghostC D 0) x + matterZeroFree D H x

**Theorem 1.24 (original_charge_split).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.original_charge_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.original_charge_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state, Qx=c0*L0*x+b0*R0*x+zeroModeFreeCharge*x. Tensor induction lifts the ghost identity, and commutation of the two tensor factors combines the matter zero mode.

Exact source telescope: theorem original_charge_split (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) : totalCharge D H x = ghostC D 0 (L0 D H x) + ghostB D 0 (ghostR D 0 x) + zeroModeFreeCharge D H x

**Theorem 1.25 (Qhat_eq_zeroModeFree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_eq_zeroModeFree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_eq_zeroModeFree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the entire unchanged carrier, Qhat equals the explicitly defined statewise finite zero-mode-free charge. No shell or inverse-Gram hypothesis is used.

Exact source telescope: theorem Qhat_eq_zeroModeFree (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Qhat D H = zeroModeFreeCharge D H

**Theorem 1.26 (Qhat_eq_original_on_relative_shell).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_eq_original_on_relative_shell`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_eq_original_on_relative_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Qhat x equals Q x when the actual b0 x and unshifted totalL0 x vanish. The even ordinary R0-b0 commutator is required to eliminate b0*R0*x. No global equality Qhat=Q is asserted.

Exact source telescope: theorem Qhat_eq_original_on_relative_shell (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) (hb : ghostB D 0 x = 0) (hL : L0 D H x = 0) : Qhat D H x = totalCharge D H x

**Theorem 1.27 (Qhat_totalL0_comm).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_totalL0_comm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_totalL0_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two original inverse-Gram identities imply commutation of Qhat with the actual total L0. At r=0 the native rank-dependent anomaly vanishes for every rank. The separate R0 covariance uses no inverse-Gram premise.

Exact source telescope: theorem Qhat_totalL0_comm (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1) (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) : L0 D H * Qhat D H - Qhat D H * L0 D H = 0

**Theorem 1.28 (Qhat_preserves_b0_kernel).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_b0_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_b0_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the actual Qhat-b0 anticommutator proves preservation of the literal b0 kernel; this supplies the b0 part of shell preservation.

Exact source telescope: theorem Qhat_preserves_b0_kernel (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) (hx : ghostB D 0 x = 0) : ghostB D 0 (Qhat D H x) = 0

**Theorem 1.29 (Qhat_preserves_L0_kernel).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_L0_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_L0_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both original inverse-Gram identities, the actual Qhat preserves ker of the unshifted total L0. This supplies the L0 part of shell preservation.

Exact source telescope: theorem Qhat_preserves_L0_kernel (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1) (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (x : State D) (hx : L0 D H x = 0) : L0 D H (Qhat D H x) = 0

**Theorem 1.30 (Qhat_preserves_relativeMassShell).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_relativeMassShell`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_relativeMassShell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original fixed charge a, including zero, the actual Qhat preserves the literal intersection (fixedMomentum D a intersect ker b0) intersect ker totalL0. Momentum preservation reuses LatticeRelativeMassShell.totalCharge_mem_fixedMomentum and equality with the original Q on this domain. The two kernel laws complete the proof; no stability certificate or nilpotence premise is assumed.

Exact source telescope: theorem Qhat_preserves_relativeMassShell (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1) (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (a : Charge D) (x : State D) (hx : x ∈ LatticeRelativeMassShell.relativeMassShell D H a) : Qhat D H x ∈ LatticeRelativeMassShell.relativeMassShell D H a

**Definition 1.31 (relativeQhat).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.relativeQhat`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.relativeQhat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine linear endomorphism of the original relativeMassShell restricts the explicit finite zeroModeFreeCharge. The proved equality with Qhat transports its preservation law. Its ambient action equals Qhat x and the original Q x on this literal shell; nilpotence is not built into this endomorphism.

Exact source telescope: def relativeQhat (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1) (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (a : Charge D) : Module.End ℂ (LatticeRelativeMassShell.relativeMassShell D H a)

These are repository-derived algebraic results; no literature novelty is claimed. Nilpotence, strict raising and energy estimates, HPL hypotheses and construction, BRST cohomology, no-ghost, full Monster moonshine, VOA/CFT, anomaly fusion, physical strings and AdS/CFT remain separate unfinished work. A supplier identity alone proves none of those completions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.L0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_b_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_eq_original_on_relative_shell`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_eq_zeroModeFree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_L0_kernel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_b0_kernel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_preserves_relativeMassShell`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.Qhat_totalL0_comm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.State`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector_fix_of_ker`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.bZeroProjector_isProj`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector_fix_of_ker`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cZeroProjector_isProj`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.cubicZeroFree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostB_bZeroProjector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostC_cZeroProjector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghostZeroFree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_b_zero_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_c_zero_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_zero_mixed`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.ghost_zero_split`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.matterZeroFree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.matter_zero_split`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.original_charge_split`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.relativeQhat`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.totalL0_b_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.zeroModeDecomposition`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode.zeroModeFreeCharge`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostChargeTensor](../../Quantum/Fermionic/BcGhostChargeTensor.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostSquare](../../Quantum/Fermionic/BcGhostSquare.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCovariance](LatticeMatterGhostCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell](LatticeRelativeMassShell.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](../LatticeSugawaraVirasoro.md)
