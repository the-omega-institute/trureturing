import Reg.D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter
import D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil
open _root_.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter
open private zeroLattice zeroPositive from
  Reg.D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private dependence from Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter

namespace Reg.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    Summable (fun e : ℚ => ‖sectorTraceTerm D hD H hHG hGH a τ e‖) ∧
      r.readout () () (sectorCharacter D hD H hHG hGH a (-1 / τ))
        (weilS D (fun b => sectorCharacter D hD H hHG hGH b τ) a)

private theorem sourceBridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform)) ↔
      arena.Law actual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists zeroLattice zeroPositive
  exact (h zeroLattice zeroPositive H hHG hGH 0 Complex.I (by simp)).2

def family : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp lattice_sector_character_s_transform,
    rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance
