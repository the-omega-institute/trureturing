import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
import Reg.Support.SingleDependentReadout

/-! The strict separation relation is observed in the complete original result. -/

set_option linter.style.longLine false

namespace Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open _root_.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open Matrix

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n ℓ : ℕ), 2 ≤ m → m < n → 2 ≤ ℓ → ℓ ≤ m ^ 2 →
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ ∧ traceNorm (realign ρ) ≤ 1 ∧
      ∃ c' : ℝ, (∀ σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        IsSeparable σ → esymmSV ℓ (realign σ) ≤ c') ∧
        R.readout () () c' (esymmSV ℓ (realign ρ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, hρ, hnorm, c, hsep, hbad⟩ :=
    h 2 3 2 (by decide) (by decide) (by decide) (by decide)
  exact hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
  exact lt_irrefl _ hbad

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2

/-! The complete prescribed-spectrum existence laws retain density and norm. -/
set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open _root_.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Multiset ℝ) (fun _ => Multiset ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : Multiset ℝ), {1}, ?_⟩
  intro he
  have hbad : ({1} : Multiset ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  simp at hbad

abbrev arena_uniform_witness : Arena where
  signature := signature
  Law R := ∀ (m n : ℕ), 2 ≤ m → m ^ 3 ≤ n →
    let a : ℝ := 1 / ((m : ℝ)^2)
    let b : ℝ := (1 - a) / ((m : ℝ)^2 - 1)
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ ∧ traceNorm (realign ρ) = 1 ∧
      R.readout () () (Finset.univ.val.map (singularVector (realign ρ)))
        (Multiset.replicate (m ^ 2 - 1) b + {a})
private theorem rejected_uniform_witness : ¬ arena_uniform_witness.Law rejected := by
  intro h
  obtain ⟨ρ, hρ, hnorm, hbad⟩ := h 2 8 (by decide) (by decide)
  exact hbad
def source_uniform_witness : Registration arena_uniform_witness (type_of% @uniform_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_witness, rejected, rejected_uniform_witness⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_uniform_witness.Law actual rejected rejected_uniform_witness
  dependence := dependence
def registration_uniform_witness :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.uniform_witness)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses.unit_uniform_witness
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses.source_uniform_witness
  realizationSource := none
  generated := false
  arena := .source ⟨arena_uniform_witness⟩
  objectArena := .source ⟨arena_uniform_witness⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_uniform_witness ⟨source_uniform_witness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_main_witness : Arena where
  signature := signature
  Law R := ∀ (m n : ℕ), 2 ≤ m → m < n → n < m ^ 3 - m →
    let a : ℝ := 1 / Real.sqrt ((m : ℝ) * n)
    let b : ℝ := (1 - a) / ((m : ℝ)^2 - 1)
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ ∧ traceNorm (realign ρ) = 1 ∧
      R.readout () () (Finset.univ.val.map (singularVector (realign ρ)))
        (Multiset.replicate (m ^ 2 - 1) b + {a})
private theorem rejected_main_witness : ¬ arena_main_witness.Law rejected := by
  intro h
  obtain ⟨ρ, hρ, hnorm, hbad⟩ := h 2 3 (by decide) (by decide) (by decide)
  exact hbad
def source_main_witness : Registration arena_main_witness (type_of% @main_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@main_witness, rejected, rejected_main_witness⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_main_witness.Law actual rejected rejected_main_witness
  dependence := dependence
def registration_main_witness :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.main_witness)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses.unit_main_witness
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses.source_main_witness
  realizationSource := none
  generated := false
  arena := .source ⟨arena_main_witness⟩
  objectArena := .source ⟨arena_main_witness⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_main_witness ⟨source_main_witness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_supported_witness : Arena where
  signature := signature
  Law R := ∀ (m q n : ℕ), 2 ≤ m → 1 ≤ q → q ≤ m ^ 2 → m * q ≤ n →
    let a : ℝ := 1 / ((m : ℝ) * Real.sqrt q)
    let b : ℝ := (1 - a) / ((m : ℝ)^2 - 1)
    ∃ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ ∧ traceNorm (realign ρ) = 1 ∧
      R.readout () () (Finset.univ.val.map (singularVector (realign ρ)))
        (Multiset.replicate (m ^ 2 - 1) b + {a})
private theorem rejected_supported_witness : ¬ arena_supported_witness.Law rejected := by
  intro h
  obtain ⟨ρ, hρ, hnorm, hbad⟩ := h 2 1 2 (by decide) (by decide) (by decide) (by decide)
  exact hbad
def source_supported_witness : Registration arena_supported_witness (type_of% @supported_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@supported_witness, rejected, rejected_supported_witness⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_supported_witness.Law actual rejected rejected_supported_witness
  dependence := dependence
def registration_supported_witness :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.supported_witness)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses.unit_supported_witness
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses.source_supported_witness
  realizationSource := none
  generated := false
  arena := .source ⟨arena_supported_witness⟩
  objectArena := .source ⟨arena_supported_witness⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_supported_witness ⟨source_supported_witness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Entanglement.Witness.LiPoonSzeP2.Witnesses
