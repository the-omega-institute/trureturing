import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/-! Source-bound audits of the actual oscillator classifier and canonical low spectrum. -/
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open Lattice.RootlessLowGrades
namespace Reg.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem zeroPositive : Matrix.PosDef (zeroLattice.G.map (Int.cast : ℤ → ℝ)) := by
  constructor
  · ext i; exact Fin.elim0 i
  · intro x hx
    exact (hx (by ext i; exact Fin.elim0 i)).elim
private theorem zeroRootless : ∀ a : Charge zeroLattice, bilinear zeroLattice a a ≠ 2 := by
  intro a
  simp [bilinear, zeroLattice]
private def oscillatorProbe : LatticeData where
  rank := 1
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intro i; exact ⟨0, by simp⟩

namespace Classification
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  LatticeData Exponent (fun _ => ℕ)
def actual : Realization signature := realize signature
  (fun _ D d => oscillatorEnergy d) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData) (d : Exponent D), a.readout () D d = 2 →
    (∃ i : Fin D.rank, d = Finsupp.single (i, 1) 1) ∨
    (∃ i j : Fin D.rank, d = Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1)
private theorem bridge : (type_of% (@oscillator_two_classification)) ↔ arena.Law actual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  rcases h zeroLattice 0 rfl with ⟨i, _⟩ | ⟨i, _, _⟩ <;> exact Fin.elim0 i
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨oscillatorProbe, 0, Finsupp.single (⟨0, by decide⟩, 0) 1, ?_⟩
  simp [actual, realize, oscillatorEnergy, Finsupp.weight_single]
def family : Registration arena (type_of% (@oscillator_two_classification)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp oscillator_two_classification, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@oscillator_two_classification) (Realization signature) (LatticeData → Type) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades.Classification.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades.Classification.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Classification

namespace Spectrum
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
  Law a := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2),
    (∀ n : ℤ, FiniteDimensional ℂ
      ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (n : ℂ))) ∧
    a.readout 0 () (Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 0)) 1 ∧
    a.readout 1 () (Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 1)) D.rank ∧
    a.readout 2 () (Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 2))
      (D.rank + Nat.choose (D.rank + 1) 2 + Nat.card (NormFour D))
private theorem bridge : (type_of% (@actual_rootless_low_spectrum)) ↔ arena.Law actual := Iff.rfl
private theorem rejectedLaw (i : Fin 3) : ¬ arena.Law (rejected i) := by
  intro h
  have bad := h zeroLattice zeroPositive zeroRootless
  fin_cases i
  · simpa [rejected, realize] using bad.2.1
  · simpa [rejected, realize] using bad.2.2.1
  · simpa [rejected, realize] using bad.2.2.2
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hc := congrFun h 0
  simp [actual, realize] at hc
def family : Registration arena (type_of% (@actual_rootless_low_spectrum)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_rootless_low_spectrum, rejected 0, rejectedLaw 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejectedLaw i⟩
      intro j hj
      funext p x y
      simp [actual, rejected, realize, hj]
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_rootless_low_spectrum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades.Spectrum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades.Spectrum.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "arg", "fn", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "arg", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true,
        stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Spectrum
#print axioms Classification.family
#print axioms Spectrum.family
end Reg.D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
