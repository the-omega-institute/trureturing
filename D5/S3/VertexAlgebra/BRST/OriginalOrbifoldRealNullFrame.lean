/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRealNullFrame
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldRealNullFrame
   mirror-E: none(waiver:algebraic-original-orbifold-real-null-frame)
   anchors: []
   utility: none
   digest: Real normalized null frames detecting the original hyperbolic momentum. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeShellQuartet
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame

/-! The ordered hyperbolic coordinate vectors give two normalized real frames.
Their light-cone momentum scalars detect the two integral charge coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldRealNullFrame

open OriginalOrbifoldCriticalMatter (hyperbolicData)
open OriginalOrbifoldRelativeQuartet (Frame UCharge)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeLightConeCoordinates (g chargeVector)
open LatticeRealNullFrame (E_R g_R g_R_apply realCharge complexify complexify_charge
  complexify_gram complexify_conjugate conjugateVector conjugate_gram)
open OrderedHyperbolicExtension (extend new splice sum_ordered)
open private zeroLattice from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatter

/-- Both null vectors are fixed by conjugation in the original coordinates. -/
def IsRealFrame (F : Frame) : Prop :=
  conjugateVector F.ePlus = F.ePlus ∧ conjugateVector F.eMinus = F.eMinus

/-- The light-cone momentum scalar of a real frame is fixed by complex conjugation. -/
theorem pPlus_real (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    starRingEnd ℂ (F.pPlus a) = F.pPlus a := by
  have hcharge : conjugateVector (chargeVector a) = chargeVector a := by
    rw [← complexify_charge, complexify_conjugate]
  change star (g hyperbolicData F.ePlus (chargeVector a)) =
    g hyperbolicData F.ePlus (chargeVector a)
  rw [conjugate_gram, hF.1, hcharge]

private def e0 (D : LatticeData) : E_R (extend D) := splice D 0 1 0

private def e1 (D : LatticeData) : E_R (extend D) := splice D 0 0 1

private theorem gram_e0 (D : LatticeData) (v : E_R (extend D)) :
    g_R (extend D) (e0 D) v = v (new D 1) := by
  simp [g_R_apply, sum_ordered D, e0]

private theorem gram_e1 (D : LatticeData) (v : E_R (extend D)) :
    g_R (extend D) (e1 D) v = v (new D 0) := by
  simp [g_R_apply, sum_ordered D, e1]

private def frame01 : Frame where
  ePlus := complexify hyperbolicData (e0 zeroLattice)
  eMinus := complexify hyperbolicData (e1 zeroLattice)
  plus_null := by
    rw [complexify_gram, gram_e0]
    simp [e0]
  minus_null := by
    rw [complexify_gram, gram_e1]
    simp [e1]
  plus_minus := by
    rw [complexify_gram, gram_e0]
    simp [e1]

private def frame10 : Frame where
  ePlus := frame01.eMinus
  eMinus := frame01.ePlus
  plus_null := frame01.minus_null
  minus_null := frame01.plus_null
  plus_minus := frame01.minus_plus

private theorem frame01_real : IsRealFrame frame01 :=
  ⟨complexify_conjugate hyperbolicData (e0 zeroLattice),
    complexify_conjugate hyperbolicData (e1 zeroLattice)⟩

private theorem frame01_pPlus (a : UCharge) : frame01.pPlus a = (a 1 : ℂ) := by
  change g hyperbolicData (complexify hyperbolicData (e0 zeroLattice)) (chargeVector a) =
    (a (new zeroLattice 1) : ℂ)
  rw [← complexify_charge, complexify_gram, gram_e0]
  simp [realCharge]

private theorem frame10_pPlus (a : UCharge) : frame10.pPlus a = (a 0 : ℂ) := by
  change g hyperbolicData (complexify hyperbolicData (e1 zeroLattice)) (chargeVector a) =
    (a (new zeroLattice 0) : ℂ)
  rw [← complexify_charge, complexify_gram, gram_e1]
  simp [realCharge]

/-- One of the two ordered real null frames detects each nonzero original U charge. -/
theorem exists_real_frame (a : UCharge) (ha : a ≠ 0) :
    ∃ F : Frame, IsRealFrame F ∧ F.pPlus a ≠ 0 := by
  by_cases h1 : a 1 = 0
  · have h0 : a 0 ≠ 0 := by
      intro h0
      apply ha
      funext i
      exact (Fin.forall_fin_two.mpr ⟨h0, h1⟩ : ∀ j : Fin 2, a j = 0) i
    refine ⟨frame10, ⟨frame01_real.2, frame01_real.1⟩, ?_⟩
    rw [frame10_pPlus, Int.cast_ne_zero]
    exact h0
  · refine ⟨frame01, frame01_real, ?_⟩
    rw [frame01_pPlus, Int.cast_ne_zero]
    exact h1

#print axioms IsRealFrame
#print axioms pPlus_real
#print axioms exists_real_frame

end D5.S3.VertexAlgebra.OriginalOrbifoldRealNullFrame
