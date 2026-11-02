import D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound equality observation for the actual first-return classification. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitFixedSpace
open D5.S3.VertexAlgebra.Lattice.CyclicGroundOrbitBasis
open D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeAllStateField

noncomputable section
namespace Reg.Support.CyclicGroundOrbitFixedSpace

private def emptyLattice : LatticeData :=
  ⟨0, 0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩

private def unitLattice : LatticeData :=
  ⟨1, fun _ _ => 4, by intros; rfl, by intro i; exact ⟨2, rfl⟩⟩

abbrev signature : Signature where
  Params := LatticeData
  State D := Submodule ℂ (Carrier D)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := Submodule ℂ (Carrier D) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equality : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature equality := by
  intro i
  refine ⟨emptyLattice, ⊥, ⊤, ?_⟩
  intro h
  have he : (⊤ : Submodule ℂ (Carrier emptyLattice)) = ⊥ :=
    Eq.mp (congrFun h ⊥) rfl
  have hv : vacuum emptyLattice = 0 :=
    (Submodule.mem_bot ℂ).mp (he ▸ Submodule.mem_top : vacuum emptyLattice ∈ ⊥)
  exact vacuum_nonzero emptyLattice hv

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (_hg : ∀ b c, bilinear D (g b) (g c) = bilinear D b c)
    (chi : Charge D →+ D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.F₂)
    (a : NormFour D) (m : ℕ) (_hm : 0 < m) (_hperiod : g^[m] a.1 = a.1),
    let d := Function.minimalPeriod g a.1
    let u := phaseFilteredGroundOrbit D g chi d a
    R.readout () D (groundCycleSpan D g a ⊓ correctedFixedSpace D g chi)
      (if (corrected D g chi ^ d) (chargeGroundVector D a) = chargeGroundVector D a
       then Submodule.span ℂ {u} else ⊥) ∧
    (carrierCoeffEquiv D u) (a.1, 0) = 1 ∧ u ≠ 0

private theorem bad : ¬ arena.Law rejected := by
  intro h
  let a : NormFour unitLattice := ⟨fun _ => 1, by simp [bilinear, unitLattice]⟩
  exact (h unitLattice (AddEquiv.refl _) (by intros; rfl) 0 a 1 (by decide) rfl).1

def family : Registration arena (type_of% (@first_return_ground_fixed_space)) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨first_return_ground_fixed_space, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

end Reg.Support.CyclicGroundOrbitFixedSpace
