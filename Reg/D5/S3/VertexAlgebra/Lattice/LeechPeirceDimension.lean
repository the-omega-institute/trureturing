import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension

/-! Source-bound registrations for the whole-space dimension formula and actual Leech multiplicity. -/

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Lattices.Golay
open GolayEncoder IntegerLeech
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeInvolution Lattice.NormFourVirasoroVector Lattice.RootlessLowGrades
open Lattice.LeechPeirceDimension

namespace Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature := realize signature
  (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  simp [actual, realize] at hh

namespace Fiber
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData)
    (_hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (_hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D), bilinear D a a = 4 →
      R.readout () ()
        (Module.finrank ℂ ↥((fixedSpace D ⊓
          (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)) ⊓
          (mode D a 1 0).eigenspace (1 / 16 : ℂ)))
        (Nat.card {b : NormFour D // bilinear D a b.1 = 1})

private theorem bridge : (type_of% (@actual_one_sixteenth_finrank)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨D, e, a, _, _, hpos, _, hroot, _, ha, _⟩ := actual_leech_one_sixteenth_dimension
  exact h D hpos hroot a ha

def family : Registration arena (type_of% (@actual_one_sixteenth_finrank)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_one_sixteenth_finrank, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_one_sixteenth_finrank) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension.Fiber.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension.Fiber.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Fiber

namespace Numeric
abbrev arena : Arena where
  signature := signature
  Law R := ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) (a : Charge D),
    D.rank = 24 ∧ IsUnit D.G.det ∧
    (D.G.map (Int.castRingHom ℝ)).PosDef ∧
    (∀ b c : Charge D, (bilinear D b c : ℝ) =
      RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space)) ∧
    (∀ b : Charge D, bilinear D b b ≠ 2) ∧
    (e a : RealLeech.Space) = RealLeech.castLinear
      (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) ∧
    bilinear D a a = 4 ∧
    R.readout () ()
      (Module.finrank ℂ ↥((fixedSpace D ⊓
        (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)) ⊓
        (mode D a 1 0).eigenspace (1 / 16 : ℂ))) 47104

private theorem bridge :
    (type_of% (@actual_leech_one_sixteenth_dimension)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨D, e, a, _, _, _, _, _, _, _, h⟩
  exact h

def family : Registration arena (type_of% (@actual_leech_one_sixteenth_dimension)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_leech_one_sixteenth_dimension, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_leech_one_sixteenth_dimension) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension.Numeric.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension.Numeric.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Numeric

#print axioms Fiber.family
#print axioms Numeric.family
end Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension
