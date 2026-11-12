/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPureGhostPrimary
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPureGhostPrimary
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Actual pure-ghost primary criterion and unrestricted primitive orthogonality. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalTransverseRealization

/-!
SOURCE ONLY, UNCOMPILED. The actual finite physicalLift is NOT asserted to
be pure-ghost-down here. The missing preservation of that smaller subspace
under h(Q-d0) is stated explicitly in source-export.json. This file proves
what Q-closedness means once a vector really has the literal tensor shape,
and proves the resulting annihilation of ALL incoming global primitives.

The sealed neutral43 candidate already contains the original cubic Qg_down
calculation. It is reused, not re-proved, with its UNCOMPILED status inherited.
No relative condition on an incoming primitive, finite charge cut, BPZ
replacement, or integral determinant-unit premise is introduced.

Attribution: original BRST and finite HPL suppliers, the original ghost
Virasoro/Ward formulas, neutral43, and Mathlib tensor algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private slices slices_tmul_ket from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
open private Qg_down c_one_down c_high_down from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeMatterGhostCoupling LatticeBRST
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing
open D5.S3.Quantum.Fermionic CountableOccupationFock

variable {D : LatticeData}

/-- Weight one and all strictly positive modes of the ACTUAL Sugawara
operator, on the original all-charge matter carrier. -/
def WeightOnePrimary (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) : Prop :=
  sugawaraMode D H 0 v = v ∧ ∀ m : ℤ, 0 < m → sugawaraMode D H m v = 0

private theorem b_nonnegative_down (m : ℤ) (hm : 0 ≤ m) :
    BcGhostFock.b m (ket {1}) = 0 := by
  have hcut : ¬m ≤ -2 := by omega
  have hsite : 2 * (m+1).toNat + 1 ≠ 1 := by omega
  simp [BcGhostFock.b, hcut, not_lt.mpr hm, annihilate_ket, hsite]

private theorem L_positive_down (m : ℤ) (hm : 0 < m) :
    BcGhostVirasoro.L m (ket {1}) = 0 := by
  have h := LinearMap.congr_fun (BcGhostVirasoro.ward_c m 1)
    CountableOccupationFock.vacuum
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    BcGhostFock.ghost_vacuum.2.2.1, L_vacuum_nonneg m (by omega),
    BcGhostFock.ghost_vacuum.2.1 (m+1) (by omega), map_zero, sub_zero,
    smul_zero] using h

private theorem closed_down_nonnegative
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D)
    (hv : totalCharge D H (v ⊗ₜ[ℂ] ket {1}) = 0) (m : ℤ) (hm : 0 ≤ m) :
    sugawaraMode D H m v = if m = 0 then v else 0 := by
  have hb : ghostB D m (v ⊗ₜ[ℂ] ket {1}) = 0 := by
    change v ⊗ₜ[ℂ] BcGhostFock.b m (ket {1}) = 0
    rw [b_nonnegative_down m hm, TensorProduct.tmul_zero]
  have h := LinearMap.congr_fun (total_ward_b D H m) (v ⊗ₜ[ℂ] ket {1})
  change totalCharge D H (ghostB D m (v ⊗ₜ[ℂ] ket {1})) +
    ghostB D m (totalCharge D H (v ⊗ₜ[ℂ] ket {1})) =
      sugawaraMode D H m v ⊗ₜ[ℂ] ket {1} +
        v ⊗ₜ[ℂ] BcGhostVirasoro.L m (ket {1}) at h
  rw [hb, hv, map_zero, map_zero, zero_add] at h
  by_cases hz : m = 0
  · subst m
    have hd : BcGhostVirasoro.L 0 (ket {1}) = -ket {1} := by
      simpa only [BcGhostFock.ghost_vacuum.2.2.1] using BcGhostRelativeEnergy.L_zero_down
    rw [hd, TensorProduct.tmul_neg] at h
    have hc := congrArg (fun x : State D => slices D x {1}) h
    have he : (0 : Carrier D) = sugawaraMode D H 0 v - v := by
      simpa only [map_zero, Finsupp.zero_apply, map_add, map_neg,
        Finsupp.add_apply, Finsupp.neg_apply, slices_tmul_ket,
        Finsupp.single_eq_same, sub_eq_add_neg] using hc
    simpa using sub_eq_zero.mp he.symm
  · rw [L_positive_down m (by omega), TensorProduct.tmul_zero, add_zero] at h
    have hc := congrArg (fun x : State D => slices D x {1}) h
    have he : (0 : Carrier D) = sugawaraMode D H m v := by
      simpa only [map_zero, Finsupp.zero_apply, slices_tmul_ket,
        Finsupp.single_eq_same] using hc
    simpa only [if_neg hz] using he.symm

/-- Exact pure-down criterion. The forward direction extracts the original
Virasoro equations using the actual b_m Ward identities, and the reverse
direction evaluates the original locally finite coupling and cubic charge.
It holds at arbitrary rank, arbitrary charge support and arbitrary H. -/
theorem closed_down_iff_primary
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D) :
    totalCharge D H (v ⊗ₜ[ℂ] ket {1}) = 0 ↔ WeightOnePrimary H v := by
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · simpa using closed_down_nonnegative H v hv 0 (by omega)
    · intro m hm
      simpa only [if_neg (ne_of_gt hm)] using closed_down_nonnegative H v hv m (by omega)
  · rintro ⟨hzero, hpositive⟩
    have hterm (m : ℤ) (hm : m ≠ 0) :
        summand D H m (v ⊗ₜ[ℂ] ket {1}) = 0 := by
      change sugawaraMode D H m v ⊗ₜ[ℂ] BcGhostFock.c (-m) (ket {1}) = 0
      by_cases hpos : 0 < m
      · rw [hpositive m hpos, TensorProduct.zero_tmul]
      · have hneg : m < 0 := by omega
        by_cases hminus : m = -1
        · subst m
          rw [show -(-1 : ℤ) = 1 by omega, c_one_down, TensorProduct.tmul_zero]
        · rw [c_high_down (-m) (by omega), TensorProduct.tmul_zero]
    have ht : T D H (v ⊗ₜ[ℂ] ket {1}) =
        v ⊗ₜ[ℂ] BcGhostFock.c 0 (ket {1}) := by
      change (∑ᶠ m : ℤ, summand D H m (v ⊗ₜ[ℂ] ket {1})) = _
      rw [finsum_eq_single _ 0 hterm]
      change sugawaraMode D H 0 v ⊗ₜ[ℂ] BcGhostFock.c (-0) (ket {1}) = _
      rw [hzero, neg_zero]
    simp only [totalCharge, LinearMap.add_apply, ht, ghostCharge,
      TensorProduct.map_tmul, LinearMap.id_apply, Qg_down,
      TensorProduct.tmul_neg, add_neg_cancel]

private theorem ghostR0_down : BcGhostBRST.R 0 (ket {1}) = 0 := by
  have hterm (p : ℤ) : BcGhostBRST.rTerm 0 p (ket {1}) = 0 := by
    by_cases hz : p = 0
    · subst p
      simp [BcGhostBRST.rTerm]
    · by_cases hp : 0 < p
      · have hcp : BcGhostFock.c p (ket {1}) = 0 := by
          by_cases hp1 : p = 1
          · simpa [hp1] using c_one_down
          · exact c_high_down p (by omega)
        have hc := LinearMap.congr_fun (BcGhostFock.ghost_c_car p (-p)) (ket {1})
        have hz' : BcGhostFock.c p (BcGhostFock.c (-p) (ket {1})) = 0 := by
          simpa only [LinearMap.add_apply, Module.End.mul_apply, hcp,
            map_zero, add_zero, LinearMap.zero_apply] using hc
        simp [BcGhostBRST.rTerm, Module.End.mul_apply, hz']
      · have hn : 0 < -p := by omega
        have hcn : BcGhostFock.c (-p) (ket {1}) = 0 := by
          by_cases hp1 : -p = 1
          · simpa [hp1] using c_one_down
          · exact c_high_down (-p) (by omega)
        simp [BcGhostBRST.rTerm, Module.End.mul_apply, hcn]
  change (∑ᶠ p : ℤ, BcGhostBRST.rTerm 0 p (ket {1})) = 0
  simp only [hterm, finsum_zero]

/-- Against an actual weight-one primary times ket{1}, EVERY original global
Q primitive is annihilated. The primitive u is an arbitrary State D, without
relative, ghost-number, charge, or energy hypotheses. This is the unrestricted
primitive bridge needed after the still-missing HPL pure-down theorem. -/
theorem statePairing_boundary_primary
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : State D) (v : Carrier D) (hv : WeightOnePrimary H v) :
    statePairing D (totalCharge D H u) (v ⊗ₜ[ℂ] ket {1}) = 0 := by
  have hq : totalCharge D H (v ⊗ₜ[ℂ] ket {1}) = 0 :=
    (closed_down_iff_primary H v).mpr hv
  have hr : ghostR D 0 (v ⊗ₜ[ℂ] ket {1}) = 0 := by
    change v ⊗ₜ[ℂ] BcGhostBRST.R 0 (ket {1}) = 0
    rw [ghostR0_down, TensorProduct.tmul_zero]
  have hw := LinearMap.congr_fun (total_ward_c D H 0) (v ⊗ₜ[ℂ] ket {1})
  have hqc : totalCharge D H (ghostC D 0 (v ⊗ₜ[ℂ] ket {1})) = 0 := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hq,
      map_zero, add_zero, hr] using hw
  change Hmg (conjugation D (totalCharge D H u))
    (ghostC D 0 (v ⊗ₜ[ℂ] ket {1})) = 0
  rw [conjugation_totalCharge H hHG hGH, Hmg_totalCharge H hHG hGH,
    hqc, Hmg_zero_right]

-- The second slot uses the already-proved symmetric state form; retain this
-- exact full-scope check anonymously rather than adding a bind-only wrapper.
example (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : State D) (v : Carrier D) (hv : WeightOnePrimary H v) :
    statePairing D (v ⊗ₜ[ℂ] ket {1}) (totalCharge D H u) = 0 := by
  rw [statePairing_symmetric]
  exact statePairing_boundary_primary H h26 hHG hGH u v hv

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary
