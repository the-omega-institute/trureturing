/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetGroundCompression
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetGroundCompression
   mirror-E: none(source-only)
   anchors: []
   utility: none
   digest: Literal original-Q compression on the full zero-count quartet ground. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open D5.S3.VertexAlgebra.LatticeBRST
open D5.S3.VertexAlgebra.LatticeQuartetContraction
open D5.S3.VertexAlgebra.LatticeQuartetContraction.GC
open D5.S3.VertexAlgebra.LatticeBRSTModeFiltration
open D5.S3.VertexAlgebra.LatticeBRSTFullOriginalRaising
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

private theorem exponentDegree_of_noLongitudinal (m : Exponents t)
    (hm : NoLongitudinal m) : exponentDegree m = 0 := by
  classical
  change (∑ x ∈ m.support, (m x : ℤ) * variableWeight x) = 0
  apply Finset.sum_eq_zero
  rintro ⟨l,r⟩ hx
  by_cases hp : l = plus t
  · subst l
    simp [(hm r).1]
  · by_cases hn : l = minus t
    · subst l
      simp [(hm r).2]
    · simp [variableWeight, hp, hn]

private theorem zero_count_degree (i : StateIndex D t)
    (hi : totalCount i = 0) : degree i = 0 ∨ degree i = 1 := by
  classical
  obtain ⟨hm,hS⟩ := (totalCount_zero_iff i).mp hi
  have he := exponentDegree_of_noLongitudinal i.1.2 hm
  rcases hS with hS | hS
  · left
    norm_num [degree, he, hS, D5.S3.Quantum.Fermionic.BcGhostCharge.charge, Finset.filter_singleton]
  · right
    norm_num [degree, he, hS, D5.S3.Quantum.Fermionic.BcGhostCharge.charge, Finset.filter_insert,
      Finset.filter_singleton]

private theorem P0_actual_coefficient (v : LatticeQuartetContraction.State D)
    (i : StateIndex D t) :
    (actualBasis F B).repr (P0 F B v) i =
      (if totalCount i = 0 then (1 : ℂ) else 0) *
        (actualBasis F B).repr v i := by
  classical
  have hd : P0 F B = diagonal (actualBasis F B)
      (fun j => if totalCount j = 0 then (1 : ℂ) else 0) := by
    apply (actualBasis F B).ext
    intro j
    rw [P0_basis, diagonal_basis]
  rw [hd, D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_coefficient]

private theorem count_insert_three (S : Finset ℕ) (h3 : 3 ∉ S) :
    GC.count (insert 3 S) = GC.count S := by
  have he : ((insert 3 S).erase 1).erase 3 = (S.erase 1).erase 3 := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_insert]
    aesop
  change (((insert 3 S).erase 1).erase 3).card + (if 1 ∈ insert 3 S then 0 else 1) =
    ((S.erase 1).erase 3).card + (if 1 ∈ S then 0 else 1)
  rw [he]
  simp only [Finset.mem_insert, show ¬(1 : ℕ) = 3 from by decide, false_or]

private theorem totalCount_insert_three (i : StateIndex D t) (h3 : 3 ∉ i.2) :
    totalCount (⟨i.1, insert 3 i.2⟩ : StateIndex D t) = totalCount i := by
  simp only [totalCount]
  rw [count_insert_three i.2 h3]

private theorem ghostC_basis_action (i : StateIndex D t) :
    ghostC D 0 (actualBasis F B i) =
      if 3 ∈ i.2 then 0 else
        phase 3 i.2 • actualBasis F B (⟨i.1, insert 3 i.2⟩) := by
  classical
  rcases i with ⟨⟨p,m⟩,S⟩
  rw [actualBasis_apply (F := F) (B := B) p m S]
  change tp (1 : Module.End ℂ (Carrier D)) (c 0)
    (sector F B p (MvPolynomial.monomial m 1) (ket S)) =
      if 3 ∈ S then 0 else
        phase 3 S • actualBasis F B (⟨⟨p,m⟩, insert 3 S⟩)
  rw [ghost_sector]
  by_cases h3 : 3 ∈ S
  · simp [c, create_ket, h3, sector]
  · rw [show c 0 = create 3 by norm_num [c], create_ket]
    simp only [if_neg h3]
    rw [sector_smul_right, actualBasis_apply (F := F) (B := B) p m (insert 3 S)]

private theorem ghostC_basis_zero (j : StateIndex D t)
    (hj : totalCount j = 0) (hd : degree j = 1) :
    ghostC D 0 (actualBasis F B j) = 0 := by
  classical
  obtain ⟨hm,hS⟩ := (totalCount_zero_iff j).mp hj
  have hS13 : j.2 = {1,3} := by
    rcases hS with h | h
    · have he := exponentDegree_of_noLongitudinal j.1.2 hm
      have hd0 : degree j = 0 := by
        norm_num [degree, he, h, D5.S3.Quantum.Fermionic.BcGhostCharge.charge, Finset.filter_singleton]
      omega
    · exact h
  rw [ghostC_basis_action F B j]
  simp [hS13]

private theorem P0_commutes_ghostC :
    P0 F B * ghostC D 0 = ghostC D 0 * P0 F B := by
  classical
  apply (actualBasis F B).ext
  intro i
  change P0 F B (ghostC D 0 (actualBasis F B i)) =
    ghostC D 0 (P0 F B (actualBasis F B i))
  rw [ghostC_basis_action F B i, P0_basis, map_smul]
  by_cases h3 : 3 ∈ i.2
  · rw [ghostC_basis_action F B i]
    simp [h3]
  · rw [ghostC_basis_action F B i]
    have hcount := totalCount_insert_three i h3
    simp [if_neg h3, map_smul, P0_basis, hcount, smul_smul, mul_comm]

private theorem projected_charge_rewrite
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) :
    P0 F B * totalCharge D H * P0 F B =
      P0 F B * (totalCharge D H - d0 F p) * P0 F B := by
  calc
    P0 F B * totalCharge D H * P0 F B =
        P0 F B * (totalCharge D H - d0 F p) * P0 F B +
          P0 F B * d0 F p * P0 F B := by
      rw [mul_sub, sub_mul, sub_add_cancel]
    _ = P0 F B * (totalCharge D H - d0 F p) * P0 F B := by
      rw [P0_mul_d0 F B p, zero_mul, add_zero]

private theorem ghostC_projected_remainder_basis_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : StateIndex D t) (hi : totalCount i = 0) :
    ghostC D 0
        ((P0 F B * (totalCharge D H - d0 F i.1.1) * P0 F B)
          (actualBasis F B i)) = 0 := by
  classical
  simp only [Module.End.mul_apply]
  rw [P0_basis, if_pos hi, one_smul]
  let y : LatticeQuartetContraction.State D :=
    (totalCharge D H - d0 F i.1.1) (actualBasis F B i)
  change ghostC D 0 (P0 F B y) = 0
  rw [← basis_expand (actualBasis F B) (P0 F B y)]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  have hcoef : (actualBasis F B).repr (P0 F B y) j ≠ 0 :=
    Finsupp.mem_support_iff.mp hj
  have hP := P0_actual_coefficient F B y j
  have hcount : totalCount j = 0 := by
    by_contra hn
    apply hcoef
    rw [hP]
    simp [hn]
  have hy : (actualBasis F B).repr y j ≠ 0 := by
    intro hz
    apply hcoef
    rw [hP, hz]
    simp
  have hraise : degree i + 1 ≤ degree j := by
    simpa [y] using
      (full_remainder_fixed_charge_basis_raises F B H hHG hGH
        i.1.1 i j rfl hy)
  have hdj : degree j = 1 := by
    have hiDegree := zero_count_degree i hi
    have hjDegree := zero_count_degree j hcount
    omega
  rw [ghostC_basis_zero F B j hcount hdj]
  simp

private theorem ghostC_projected_total_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    ghostC D 0 * P0 F B * totalCharge D H * P0 F B = 0 := by
  classical
  apply (actualBasis F B).ext
  intro i
  rw [show ghostC D 0 * P0 F B * totalCharge D H * P0 F B =
      ghostC D 0 * (P0 F B * totalCharge D H * P0 F B) by noncomm_ring]
  rw [projected_charge_rewrite F B H i.1.1]
  change ghostC D 0
      ((P0 F B * (totalCharge D H - d0 F i.1.1) * P0 F B)
        (actualBasis F B i)) = 0
  by_cases hi : totalCount i = 0
  · exact ghostC_projected_remainder_basis_zero F B H hHG hGH i hi
  · simp only [Module.End.mul_apply]
    rw [P0_basis, if_neg hi, zero_smul, map_zero, map_zero, map_zero]

private theorem actual_P0_commutes_b :
    P0 F B * ghostB D 0 = ghostB D 0 * P0 F B := by
  change P0 F B * ghostB0 = ghostB0 * P0 F B
  exact P0_commutes_b0 F B

/-- Literal full-state original-Q compression on the actual zero-count projector. -/
theorem original_Q_ground_compression
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    P0 F B * LatticeBRST.totalCharge D H * P0 F B =
      P0 F B * ghostC D 0 *
        (matterMode D H 0 + ghostVirasoro D 0) * P0 F B := by
  let P : Module.End ℂ (LatticeQuartetContraction.State D) := P0 F B
  let Q : Module.End ℂ (LatticeQuartetContraction.State D) := LatticeBRST.totalCharge D H
  let C : Module.End ℂ (LatticeQuartetContraction.State D) := P * Q * P
  let b : Module.End ℂ (LatticeQuartetContraction.State D) := ghostB D 0
  let c : Module.End ℂ (LatticeQuartetContraction.State D) := ghostC D 0
  let L : Module.End ℂ (LatticeQuartetContraction.State D) :=
    matterMode D H 0 + ghostVirasoro D 0
  have hCzero : c * C = 0 := by
    dsimp [c, C, P, Q]
    simpa only [mul_assoc] using
      (ghostC_projected_total_zero F B H hHG hGH)
  have hPc : P * c = c * P := by
    dsimp [P, c]
    exact P0_commutes_ghostC F B
  have hPb : P * b = b * P := by
    dsimp [P, b]
    exact actual_P0_commutes_b F B
  have hward : Q * b + b * Q = L := by
    dsimp [Q, b, L]
    exact total_ward_b D H 0
  have hcompressed : C * b + b * C = P * L * P := by
    calc
      C * b + b * C = P * Q * (P * b) + (b * P) * Q * P := by
        dsimp [C]
        noncomm_ring
      _ = P * Q * (b * P) + (P * b) * Q * P := by
        exact congrArg₂ (· + ·)
          (congrArg (fun z => P * Q * z) hPb)
          (congrArg (fun z => z * Q * P) hPb.symm)
      _ = P * (Q * b + b * Q) * P := by noncomm_ring
      _ = P * L * P := by rw [hward]
  have hfix : C = c * b * C := by
    have hcar : b * c + c * b =
        (1 : Module.End ℂ (LatticeQuartetContraction.State D)) :=
      D5.S3.VertexAlgebra.LatticeBRSTRelativeZeroMode.ghost_zero_mixed D
    calc
      C = (b * c + c * b) * C := by rw [hcar, one_mul]
      _ = b * c * C + c * b * C := by noncomm_ring
      _ = b * (c * C) + c * b * C := by rw [mul_assoc b c C]
      _ = c * b * C := by rw [hCzero, mul_zero, zero_add]
  have hleft : c * (C * b + b * C) = C := by
    calc
      c * (C * b + b * C) = c * C * b + c * b * C := by noncomm_ring
      _ = c * b * C := by rw [hCzero, zero_mul, zero_add]
      _ = C := hfix.symm
  have hfinal : C = P * c * L * P := by
    calc
      C = c * (C * b + b * C) := hleft.symm
      _ = c * (P * L * P) := by rw [hcompressed]
      _ = (c * P) * L * P := by noncomm_ring
      _ = (P * c) * L * P := by rw [hPc]
      _ = P * c * L * P := by noncomm_ring
  simpa [C, P, Q, c, L] using hfinal

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression
