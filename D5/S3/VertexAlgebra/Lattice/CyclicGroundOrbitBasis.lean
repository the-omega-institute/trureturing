/- GID: D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitBasis
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/CyclicGroundOrbitBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Phase-filtered charged-ground orbit vectors are fixed by the actual cyclic lift. -/

import D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

/-!
For a finite-order actual cyclic lift, averaging an actual charged ground
vector over one full period produces the phase-filtered orbit vector.  The
proof is a literal finite geometric-sum argument on the existing carrier;
the phase is carried by `CyclicIsometryLift.corrected`, so no permutation
module or shell-count assumption is hidden in the statement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitBasis

open D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open LatticeGeneratingFieldLocality
open scoped BigOperators VertexOperator
noncomputable section

def chargeGroundVector (D : LatticeData) (a : NormFour D) : Carrier D :=
  Finsupp.single a.1 1

def phaseFilteredGroundOrbit (D : LatticeData)
    (g : Charge D ≃+ Charge D) (chi : Charge D →+ F₂)
    (m : ℕ) (a : NormFour D) : Carrier D :=
  ∑ j ∈ Finset.range m,
    (corrected D g chi ^ j) (chargeGroundVector D a)

def correctedFixedSpace (D : LatticeData)
    (g : Charge D ≃+ Charge D) (chi : Charge D →+ F₂) :
    Submodule ℂ (Carrier D) :=
  LinearMap.ker ((corrected D g chi).toLinearMap - LinearMap.id)

private theorem geometric_shift {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V ≃ₗ[ℂ] V)
    (m : ℕ) (v : V) :
    T (∑ j ∈ Finset.range m, (T ^ j) v) =
      (∑ j ∈ Finset.range m, (T ^ j) v) + (T ^ m) v - v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, map_add, ih]
      rw [pow_succ', LinearEquiv.mul_apply]
      abel

theorem phaseFilteredGroundOrbit_fixed
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (chi : Charge D →+ F₂) (m : ℕ) (a : NormFour D)
    (hpow : corrected D g chi ^ m = 1) :
    phaseFilteredGroundOrbit D g chi m a ∈ correctedFixedSpace D g chi := by
  change corrected D g chi (phaseFilteredGroundOrbit D g chi m a) -
      phaseFilteredGroundOrbit D g chi m a = 0
  apply sub_eq_zero.mpr
  rw [phaseFilteredGroundOrbit, geometric_shift]
  rw [hpow]
  simp

theorem actual_normFour_phase_filtered_orbit_fixed
    (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hm : 0 < m) (hgm : ∀ a, g^[m] a = a)
    (a : NormFour D) :
    ∃ chi : Charge D →+ F₂,
      phaseFilteredGroundOrbit D g chi m a ∈ correctedFixedSpace D g chi := by
  obtain ⟨chi, _hv, _hy, _ht, hpow, _horder⟩ :=
    cyclic_lift D g hg m hm hgm
  exact ⟨chi, phaseFilteredGroundOrbit_fixed D g chi m a hpow⟩

end
end D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitBasis
