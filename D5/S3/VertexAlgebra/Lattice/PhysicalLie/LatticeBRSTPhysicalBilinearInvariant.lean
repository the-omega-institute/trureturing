/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalBilinearInvariant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalBilinearInvariant
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Unsigned invariance of the constructed form on the original global physical Lie image. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown
import D5.S3.VertexAlgebra.SourceBPZ.SuppliedGramTranspose
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import Batteries.Tactic.OpenPrivate

/-!
SOURCE_ONLY_UNCOMPILED. The global bilinear descent, all-charge primary
representatives and supplied-H BPZ imports are sealed source candidates.
Composing them here confers no native acceptance on them or this module.

The form is the existing physicalBilinearForm and the bracket is the
existing physicalImage Lie bracket. Only the middle class is represented
by a primary tensor, using equality in the original global Q quotient.
The other representatives are arbitrary physical states. The tensor
skew-adjoint computation itself holds on ALL original State D.

The finite original-field BPZ identity retains the Bakalov--Kac and source
supplier attribution. Original BRST, occupation and quotient constructions
retain their supplier attribution; the finite tensor calculation below
uses Mathlib linearity. No literature novelty is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

open private right_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private slices from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
open private state_expansion pairing_tmul_ket from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalBilinearInvariant

open LatticeGeneratingFieldLocality
open LatticeMatterGhostCoupling (State ghostB)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeBRSTCohomologyField (Cohomology originalMode)
open LatticeBRSTCohomologyBVSecondOrder (descentCurrent cohomologyCurrent)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie (physicalImage physicalStates physicalClass
  physicalStates_current)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary (WeightOnePrimary)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown (physicalClass_pure_down)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear (physicalBilinearForm
  physicalBilinearForm_representatives)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm (statePairing)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket)

variable {D : LatticeData}

-- Consumed in the all-state tensor calculation, with no physicality premise.
private theorem descentCurrent_down (v : Carrier D) :
    descentCurrent D (v ⊗ₜ[ℂ] ket {1}) =
      TensorProduct.map ((LatticeAllStateField.Y D v)[[0]]) LinearMap.id := by
  have hb : BcGhostFock.b (-1) (ket {1}) = CountableOccupationFock.vacuum := by
    norm_num [BcGhostFock.b, CountableOccupationFock.annihilate_ket,
      CountableOccupationFock.phase, CountableOccupationFock.lowerCount,
      CountableOccupationFock.vacuum, Finset.filter_singleton]
  have hs : ghostB D (-1) (v ⊗ₜ[ℂ] ket {1}) =
      v ⊗ₜ[ℂ] CountableOccupationFock.vacuum := by
    change v ⊗ₜ[ℂ] BcGhostFock.b (-1) (ket {1}) = _
    rw [hb]
  change originalMode D 0 (ghostB D (-1) (v ⊗ₜ[ℂ] ket {1})) = _
  rw [hs]
  change ((LatticeMatterGhostStateField.Y D
    (v ⊗ₜ[ℂ] CountableOccupationFock.vacuum))[[0]]) = _
  exact right_vacuum_modes D v 0

-- The accepted L0 theorem uses the supplied complex inverse identities.
-- The positive BPZ tail vanishes because the actual L1 kills the source.
private theorem source_zero_primary
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (v : Carrier D) (hv : WeightOnePrimary H v) (u w : Carrier D) :
    sourcePairing D (((LatticeAllStateField.Y D v)[[0]]) u) w =
      -sourcePairing D u (((LatticeAllStateField.Y D v)[[0]]) w) := by
  classical
  have hgrade : v ∈ LatticePositiveEnergy.grade D 1 :=
    (LatticePositiveEnergy.actualL0_eigen_iff_grade D H hHG hGH 1 v).mp
      (by simpa only [Int.cast_one, one_smul] using hv.1)
  have hL1 : sugawaraMode D H 1 v = 0 := hv.2 1 (by omega)
  rw [SourceBPZ.SuppliedGramTranspose.sourcePairing_allState
    D H hHG hGH 1 0 v hgrade u w]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hfirst : (sugawaraMode D H 1 ^ (1 : ℕ)) v = 0 := by
      simpa only [pow_one] using hL1
    have killed : (sugawaraMode D H 1 ^ j) v = 0 :=
      Module.End.pow_map_zero_of_le (show 1 ≤ j by omega) hfirst
    simp [killed]
  · simp

-- Both ghost insertion factors are literally the same Hg(ket S,c0 ket T).
-- Finite occupation expansion extends the computation to arbitrary states.
private theorem statePairing_current_primary
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (v : Carrier D) (hv : WeightOnePrimary H v) (x z : State D) :
    statePairing D (descentCurrent D (v ⊗ₜ[ℂ] ket {1}) x) z =
      -statePairing D x (descentCurrent D (v ⊗ₜ[ℂ] ket {1}) z) := by
  classical
  let A : Module.End ℂ (State D) :=
    TensorProduct.map ((LatticeAllStateField.Y D v)[[0]]) LinearMap.id
  have ht (u w : Carrier D) (S T : Finset ℕ) :
      statePairing D (A (u ⊗ₜ[ℂ] ket S)) (w ⊗ₜ[ℂ] ket T) =
        -statePairing D (u ⊗ₜ[ℂ] ket S) (A (w ⊗ₜ[ℂ] ket T)) := by
    simp only [A, TensorProduct.map_tmul, LinearMap.id_apply, pairing_tmul_ket]
    rw [source_zero_primary H hHG hGH v hv u w, neg_mul]
  simp only [descentCurrent_down]
  change statePairing D (A x) z = -statePairing D x (A z)
  calc
    statePairing D (A x) z =
        ∑ S ∈ (slices D x).support, ∑ T ∈ (slices D z).support,
          statePairing D (A ((slices D x) S ⊗ₜ[ℂ] ket S))
            ((slices D z) T ⊗ₜ[ℂ] ket T) := by
      conv_lhs => rw [← state_expansion x, ← state_expansion z]
      simp only [map_sum, LinearMap.sum_apply]
      rw [Finset.sum_comm]
    _ = ∑ S ∈ (slices D x).support, ∑ T ∈ (slices D z).support,
          -statePairing D ((slices D x) S ⊗ₜ[ℂ] ket S)
            (A ((slices D z) T ⊗ₜ[ℂ] ket T)) := by
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      exact ht _ _ S T
    _ = -statePairing D x (A z) := by
      conv_rhs => rw [← state_expansion x, ← state_expansion z]
      simp only [map_sum, LinearMap.sum_apply, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]

/-- Ordinary unsigned invariance of the ACTUAL constructed bilinear form
on ALL elements of the literal original global physical Lie image. The two
inverse equations and rank 26 are the original assumptions. No primary,
charge, frame, positivity, or restriction on incoming primitives is added. -/
theorem physicalBilinearForm_invariant
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x y z : physicalImage D H h26 hHG hGH) :
    physicalBilinearForm D H h26 hHG hGH (⁅x, y⁆) z =
      physicalBilinearForm D H h26 hHG hGH x (⁅y, z⁆) := by
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b₀, hb₀⟩ := y.property
  obtain ⟨c, hc⟩ := z.property
  obtain ⟨b, v, hbv, hv, hclass, _hprimitive⟩ :=
    physicalClass_pure_down H h26 hHG hGH b₀
  have hb : physicalClass D H h26 hHG hGH b =
      (y : Cohomology D H h26 hHG hGH) := hclass.trans hb₀
  let ba : physicalStates D H :=
    ⟨descentCurrent D b a, physicalStates_current D H hHG hGH b a⟩
  let bc : physicalStates D H :=
    ⟨descentCurrent D b c, physicalStates_current D H hHG hGH b c⟩
  have hba : physicalClass D H h26 hHG hGH ba =
      ((⁅y, x⁆ : physicalImage D H h26 hHG hGH) :
        Cohomology D H h26 hHG hGH) := by
    change cohomologyCurrent D H h26 hHG hGH
      (physicalClass D H h26 hHG hGH b) (physicalClass D H h26 hHG hGH a) =
        cohomologyCurrent D H h26 hHG hGH (y : Cohomology D H h26 hHG hGH)
          (x : Cohomology D H h26 hHG hGH)
    rw [hb, ha]
  have hbc : physicalClass D H h26 hHG hGH bc =
      ((⁅y, z⁆ : physicalImage D H h26 hHG hGH) :
        Cohomology D H h26 hHG hGH) := by
    change cohomologyCurrent D H h26 hHG hGH
      (physicalClass D H h26 hHG hGH b) (physicalClass D H h26 hHG hGH c) =
        cohomologyCurrent D H h26 hHG hGH (y : Cohomology D H h26 hHG hGH)
          (z : Cohomology D H h26 hHG hGH)
    rw [hb, hc]
  have hskew :
      physicalBilinearForm D H h26 hHG hGH (⁅y, x⁆) z =
        -physicalBilinearForm D H h26 hHG hGH x (⁅y, z⁆) := by
    rw [physicalBilinearForm_representatives D H h26 hHG hGH
      (⁅y, x⁆) z ba c hba hc,
      physicalBilinearForm_representatives D H h26 hHG hGH
        x (⁅y, z⁆) a bc ha hbc]
    change statePairing D (descentCurrent D (b : State D) (a : State D))
      (c : State D) = -statePairing D (a : State D)
        (descentCurrent D (b : State D) (c : State D))
    rw [hbv]
    exact statePairing_current_primary H hHG hGH v hv a c
  calc
    physicalBilinearForm D H h26 hHG hGH (⁅x, y⁆) z =
        -physicalBilinearForm D H h26 hHG hGH (⁅y, x⁆) z := by
      rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = physicalBilinearForm D H h26 hHG hGH x (⁅y, z⁆) := by
      rw [hskew, neg_neg]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalBilinearInvariant
