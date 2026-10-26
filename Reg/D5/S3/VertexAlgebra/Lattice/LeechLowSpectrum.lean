import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Lattices.Golay
open GolayEncoder IntegerLeech
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open Lattice.RootlessLowGrades Lattice.LeechLowSpectrum

namespace Reg.D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected (i : Fin 3) : Realization signature := realize signature
  (fun j _ x y => if j = i then False else x = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice),
    D.rank = 24 ∧ IsUnit D.G.det ∧
    (D.G.map (Int.castRingHom ℝ)).PosDef ∧
    (∀ a c : Charge D, (bilinear D a c : ℝ) =
      RealLeech.pairing (e a : RealLeech.Space) (e c : RealLeech.Space)) ∧
    (∀ a : Charge D, bilinear D a a ≠ 2) ∧
    ∃ s : NormFour D ≃
        {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32},
      (∀ a : NormFour D,
        RealLeech.castLinear (s a).1 = (e a.1 : RealLeech.Space)) ∧
      Finite (NormFour D) ∧ Nat.card (NormFour D) = 196560 ∧
      (∀ n : ℤ, FiniteDimensional ℂ
        ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (n : ℂ))) ∧
      R.readout 0 ()
        (Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 0)) 1 ∧
      R.readout 1 ()
        (Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 1)) 24 ∧
      R.readout 2 ()
        (Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 2)) 196884

private theorem bridge : (type_of% (@actual_leech_low_spectrum)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law (i : Fin 3) : ¬ arena.Law (rejected i) := by
  rintro ⟨D, e, hrank, hunit, hpos, hpair, hroot, s, hs, hf, hc, hall, hzero, hone, htwo⟩
  fin_cases i
  · simpa [rejected, realize] using hzero
  · simpa [rejected, realize] using hone
  · simpa [rejected, realize] using htwo

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hc := congrFun h 0
  simp [actual, realize] at hc

def family : Registration arena (type_of% (@actual_leech_low_spectrum)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_leech_low_spectrum, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p x y
      simp [actual, rejected, realize, hj]
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_leech_low_spectrum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "body",
          "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"],
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "body",
          "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"],
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "body",
          "arg", "arg", "arg", "arg", "arg", "arg", "fn", "fn"],
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
